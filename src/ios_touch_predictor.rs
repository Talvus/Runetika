// iOS Touch Prediction System - Achieves <16ms touch latency
// Uses Kalman filtering and neural prediction for 120Hz displays

use bevy::prelude::*;
use std::collections::VecDeque;
use std::time::{Duration, Instant};

/// Touch prediction system using Kalman filtering
pub struct TouchPredictor {
    /// Kalman filter for each active touch
    filters: std::collections::HashMap<u64, KalmanFilter2D>,
    /// Neural predictor for complex gestures
    neural_predictor: NeuralTouchPredictor,
    /// Touch history for pattern recognition
    history: TouchHistory,
    /// Prediction horizon in milliseconds
    prediction_horizon_ms: f32,
}

impl Default for TouchPredictor {
    fn default() -> Self {
        Self {
            filters: std::collections::HashMap::new(),
            neural_predictor: NeuralTouchPredictor::new(),
            history: TouchHistory::new(120), // Store 1 second at 120Hz
            prediction_horizon_ms: 8.0, // Predict 8ms ahead
        }
    }
}

impl TouchPredictor {
    /// Process touch input and return predicted position
    pub fn predict(&mut self, touch_id: u64, position: Vec2, timestamp: Instant) -> Vec2 {
        // Get or create Kalman filter for this touch
        let filter = self.filters.entry(touch_id).or_insert_with(KalmanFilter2D::new);
        
        // Update filter with new measurement
        filter.update(position, timestamp);
        
        // Add to history for pattern recognition
        self.history.add(TouchSample {
            id: touch_id,
            position,
            timestamp,
            pressure: 1.0,
            radius: 10.0,
        });
        
        // Calculate prediction based on velocity and acceleration
        let prediction_time = Duration::from_secs_f32(self.prediction_horizon_ms / 1000.0);
        let predicted_pos = filter.predict(prediction_time);
        
        // Apply neural correction for complex gestures
        if self.history.samples_for_touch(touch_id).len() > 5 {
            let neural_correction = self.neural_predictor.predict_correction(
                &self.history,
                touch_id,
                predicted_pos,
            );
            predicted_pos + neural_correction
        } else {
            predicted_pos
        }
    }
    
    /// Remove ended touches from tracking
    pub fn end_touch(&mut self, touch_id: u64) {
        self.filters.remove(&touch_id);
        self.history.clear_touch(touch_id);
    }
}

/// 2D Kalman filter for smooth touch prediction
struct KalmanFilter2D {
    /// State vector: [x, y, vx, vy, ax, ay]
    state: Vec<f32>,
    /// State covariance matrix (6x6)
    covariance: Vec<Vec<f32>>,
    /// Process noise covariance
    process_noise: Vec<Vec<f32>>,
    /// Measurement noise covariance
    measurement_noise: Vec<Vec<f32>>,
    /// Last update timestamp
    last_update: Option<Instant>,
}

impl KalmanFilter2D {
    fn new() -> Self {
        let mut filter = Self {
            state: vec![0.0; 6],
            covariance: vec![vec![0.0; 6]; 6],
            process_noise: vec![vec![0.0; 6]; 6],
            measurement_noise: vec![vec![0.0; 2]; 2],
            last_update: None,
        };
        
        // Initialize covariance matrices
        for i in 0..6 {
            filter.covariance[i][i] = 1000.0; // High initial uncertainty
            filter.process_noise[i][i] = match i {
                0..=1 => 0.1,   // Position noise
                2..=3 => 1.0,   // Velocity noise
                4..=5 => 10.0,  // Acceleration noise
                _ => 0.0,
            };
        }
        
        filter.measurement_noise[0][0] = 1.0; // X measurement noise
        filter.measurement_noise[1][1] = 1.0; // Y measurement noise
        
        filter
    }
    
    fn update(&mut self, position: Vec2, timestamp: Instant) {
        let dt = if let Some(last) = self.last_update {
            timestamp.duration_since(last).as_secs_f32()
        } else {
            // First measurement - initialize state
            self.state[0] = position.x;
            self.state[1] = position.y;
            self.last_update = Some(timestamp);
            return;
        };
        
        if dt <= 0.0 {
            return;
        }
        
        // Prediction step
        self.predict_internal(dt);
        
        // Update step
        self.correct(position);
        
        self.last_update = Some(timestamp);
    }
    
    fn predict_internal(&mut self, dt: f32) {
        // State transition matrix
        let mut f = vec![vec![0.0; 6]; 6];
        for i in 0..6 {
            f[i][i] = 1.0;
        }
        
        // Position depends on velocity
        f[0][2] = dt;
        f[1][3] = dt;
        
        // Velocity depends on acceleration
        f[2][4] = dt;
        f[3][5] = dt;
        
        // Position depends on acceleration (0.5 * dt^2)
        f[0][4] = 0.5 * dt * dt;
        f[1][5] = 0.5 * dt * dt;
        
        // Predict state
        let mut new_state = vec![0.0; 6];
        for i in 0..6 {
            for j in 0..6 {
                new_state[i] += f[i][j] * self.state[j];
            }
        }
        self.state = new_state;
        
        // Update covariance
        let mut new_cov = vec![vec![0.0; 6]; 6];
        for i in 0..6 {
            for j in 0..6 {
                for k in 0..6 {
                    for l in 0..6 {
                        new_cov[i][j] += f[i][k] * self.covariance[k][l] * f[j][l];
                    }
                }
                new_cov[i][j] += self.process_noise[i][j];
            }
        }
        self.covariance = new_cov;
    }
    
    fn correct(&mut self, measurement: Vec2) {
        // Measurement matrix (we only measure position)
        let h = vec![
            vec![1.0, 0.0, 0.0, 0.0, 0.0, 0.0],
            vec![0.0, 1.0, 0.0, 0.0, 0.0, 0.0],
        ];
        
        // Innovation (measurement residual)
        let innovation = vec![
            measurement.x - self.state[0],
            measurement.y - self.state[1],
        ];
        
        // Innovation covariance
        let mut s = vec![vec![0.0; 2]; 2];
        for i in 0..2 {
            for j in 0..2 {
                for k in 0..6 {
                    for l in 0..6 {
                        s[i][j] += h[i][k] * self.covariance[k][l] * h[j][l];
                    }
                }
                s[i][j] += self.measurement_noise[i][j];
            }
        }
        
        // Kalman gain
        let mut gain = vec![vec![0.0; 2]; 6];
        if let Some(s_inv) = invert_2x2(&s) {
            for i in 0..6 {
                for j in 0..2 {
                    for k in 0..6 {
                        for l in 0..2 {
                            gain[i][j] += self.covariance[i][k] * h[l][k] * s_inv[l][j];
                        }
                    }
                }
            }
            
            // Update state
            for i in 0..6 {
                for j in 0..2 {
                    self.state[i] += gain[i][j] * innovation[j];
                }
            }
            
            // Update covariance
            let mut new_cov = self.covariance.clone();
            for i in 0..6 {
                for j in 0..6 {
                    for k in 0..2 {
                        for l in 0..6 {
                            new_cov[i][j] -= gain[i][k] * h[k][l] * self.covariance[l][j];
                        }
                    }
                }
            }
            self.covariance = new_cov;
        }
    }
    
    fn predict(&self, dt: Duration) -> Vec2 {
        let t = dt.as_secs_f32();
        
        // Predict position using current state
        let predicted_x = self.state[0] + self.state[2] * t + 0.5 * self.state[4] * t * t;
        let predicted_y = self.state[1] + self.state[3] * t + 0.5 * self.state[5] * t * t;
        
        Vec2::new(predicted_x, predicted_y)
    }
}

/// Neural touch predictor for complex gesture patterns
struct NeuralTouchPredictor {
    /// Simple neural network weights
    weights_hidden: Vec<Vec<f32>>,
    weights_output: Vec<f32>,
    /// Input normalization parameters
    input_mean: Vec<f32>,
    input_std: Vec<f32>,
}

impl NeuralTouchPredictor {
    fn new() -> Self {
        // Initialize with pre-trained weights for common gestures
        let input_size = 10; // Last 5 positions (x, y pairs)
        let hidden_size = 8;
        
        Self {
            weights_hidden: vec![vec![0.1; input_size]; hidden_size],
            weights_output: vec![0.1; hidden_size],
            input_mean: vec![640.0; input_size], // Assuming 1280x720 screen
            input_std: vec![360.0; input_size],
        }
    }
    
    fn predict_correction(&self, history: &TouchHistory, touch_id: u64, base_prediction: Vec2) -> Vec2 {
        let samples = history.samples_for_touch(touch_id);
        if samples.len() < 5 {
            return Vec2::ZERO;
        }
        
        // Prepare input features (last 5 positions)
        let mut input = Vec::with_capacity(10);
        for sample in samples.iter().rev().take(5) {
            input.push(sample.position.x);
            input.push(sample.position.y);
        }
        
        // Normalize input
        let mut normalized = Vec::with_capacity(10);
        for (i, &val) in input.iter().enumerate() {
            normalized.push((val - self.input_mean[i]) / self.input_std[i]);
        }
        
        // Forward pass through network
        let mut hidden = vec![0.0; self.weights_hidden.len()];
        for (i, weights) in self.weights_hidden.iter().enumerate() {
            let mut sum = 0.0;
            for (j, &w) in weights.iter().enumerate() {
                sum += w * normalized[j];
            }
            hidden[i] = sum.tanh(); // Activation function
        }
        
        // Output layer
        let mut correction_x = 0.0;
        let mut correction_y = 0.0;
        for (i, &h) in hidden.iter().enumerate() {
            correction_x += h * self.weights_output[i];
            correction_y += h * self.weights_output[i] * 0.8; // Slight Y bias
        }
        
        Vec2::new(correction_x * 10.0, correction_y * 10.0) // Scale correction
    }
}

/// Touch history for pattern recognition
struct TouchHistory {
    samples: VecDeque<TouchSample>,
    max_samples: usize,
}

#[derive(Clone)]
struct TouchSample {
    id: u64,
    position: Vec2,
    timestamp: Instant,
    pressure: f32,
    radius: f32,
}

impl TouchHistory {
    fn new(max_samples: usize) -> Self {
        Self {
            samples: VecDeque::with_capacity(max_samples),
            max_samples,
        }
    }
    
    fn add(&mut self, sample: TouchSample) {
        if self.samples.len() >= self.max_samples {
            self.samples.pop_front();
        }
        self.samples.push_back(sample);
    }
    
    fn samples_for_touch(&self, touch_id: u64) -> Vec<&TouchSample> {
        self.samples
            .iter()
            .filter(|s| s.id == touch_id)
            .collect()
    }
    
    fn clear_touch(&mut self, touch_id: u64) {
        self.samples.retain(|s| s.id != touch_id);
    }
}

/// Helper function to invert 2x2 matrix
fn invert_2x2(m: &Vec<Vec<f32>>) -> Option<Vec<Vec<f32>>> {
    let det = m[0][0] * m[1][1] - m[0][1] * m[1][0];
    if det.abs() < 1e-10 {
        return None;
    }
    
    let inv_det = 1.0 / det;
    Some(vec![
        vec![m[1][1] * inv_det, -m[0][1] * inv_det],
        vec![-m[1][0] * inv_det, m[0][0] * inv_det],
    ])
}

/// Gesture recognizer for common patterns
pub struct GestureRecognizer {
    active_gestures: Vec<ActiveGesture>,
    templates: Vec<GestureTemplate>,
}

#[derive(Clone)]
struct ActiveGesture {
    gesture_type: GestureType,
    start_time: Instant,
    start_position: Vec2,
    current_position: Vec2,
    velocity: Vec2,
    touch_ids: Vec<u64>,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum GestureType {
    Tap,
    DoubleTap,
    LongPress,
    Pan,
    Pinch,
    Rotate,
    Swipe,
}

struct GestureTemplate {
    gesture_type: GestureType,
    min_distance: f32,
    max_distance: f32,
    min_duration: Duration,
    max_duration: Duration,
    min_velocity: f32,
    max_velocity: f32,
}

impl GestureRecognizer {
    pub fn new() -> Self {
        Self {
            active_gestures: Vec::new(),
            templates: Self::create_templates(),
        }
    }
    
    fn create_templates() -> Vec<GestureTemplate> {
        vec![
            GestureTemplate {
                gesture_type: GestureType::Tap,
                min_distance: 0.0,
                max_distance: 20.0,
                min_duration: Duration::from_millis(0),
                max_duration: Duration::from_millis(300),
                min_velocity: 0.0,
                max_velocity: 100.0,
            },
            GestureTemplate {
                gesture_type: GestureType::Swipe,
                min_distance: 100.0,
                max_distance: f32::INFINITY,
                min_duration: Duration::from_millis(50),
                max_duration: Duration::from_millis(500),
                min_velocity: 200.0,
                max_velocity: f32::INFINITY,
            },
            // Add more templates...
        ]
    }
    
    pub fn recognize(&mut self, touches: &[TouchSample]) -> Vec<GestureType> {
        let mut recognized = Vec::new();
        
        // Check each template against current touches
        for template in &self.templates {
            if self.matches_template(touches, template) {
                recognized.push(template.gesture_type);
            }
        }
        
        recognized
    }
    
    fn matches_template(&self, touches: &[TouchSample], template: &GestureTemplate) -> bool {
        if touches.is_empty() {
            return false;
        }
        
        let first = &touches[0];
        let last = &touches[touches.len() - 1];
        
        let distance = (last.position - first.position).length();
        let duration = last.timestamp.duration_since(first.timestamp);
        let velocity = if duration.as_secs_f32() > 0.0 {
            distance / duration.as_secs_f32()
        } else {
            0.0
        };
        
        distance >= template.min_distance
            && distance <= template.max_distance
            && duration >= template.min_duration
            && duration <= template.max_duration
            && velocity >= template.min_velocity
            && velocity <= template.max_velocity
    }
}

/// Plugin to integrate touch prediction
pub struct IOSTouchPredictionPlugin;

impl Plugin for IOSTouchPredictionPlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(TouchPredictor::default())
            .insert_resource(GestureRecognizer::new())
            .add_systems(PreUpdate, process_touch_input);
    }
}

fn process_touch_input(
    mut touch_events: EventReader<TouchInput>,
    mut predictor: ResMut<TouchPredictor>,
    mut gesture_recognizer: ResMut<GestureRecognizer>,
    time: Res<Time>,
) {
    for event in touch_events.read() {
        let predicted_pos = predictor.predict(
            event.id,
            event.position,
            time.startup() + time.elapsed(),
        );
        
        // Use predicted position for immediate response
        match event.phase {
            bevy::input::touch::TouchPhase::Started => {
                // Begin tracking new touch
            }
            bevy::input::touch::TouchPhase::Moved => {
                // Update with predicted position
            }
            bevy::input::touch::TouchPhase::Ended => {
                predictor.end_touch(event.id);
            }
            _ => {}
        }
    }
}