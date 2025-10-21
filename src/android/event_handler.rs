/// Event Handler for Android Input Events
/// Manages touch, sensor, and other Android-specific events

use bevy::prelude::*;
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;
use crate::android::jni_bridge::JniError;

/// Maximum events in queue before dropping oldest
const MAX_EVENT_QUEUE_SIZE: usize = 1000;

/// Touch action constants matching Android MotionEvent
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TouchAction {
    Down = 0,
    Up = 1,
    Move = 2,
    Cancel = 3,
    PointerDown = 5,
    PointerUp = 6,
}

impl From<i32> for TouchAction {
    fn from(value: i32) -> Self {
        match value {
            0 => TouchAction::Down,
            1 => TouchAction::Up,
            2 => TouchAction::Move,
            3 => TouchAction::Cancel,
            5 => TouchAction::PointerDown,
            6 => TouchAction::PointerUp,
            _ => TouchAction::Cancel,
        }
    }
}

/// Touch event data
#[derive(Debug, Clone)]
pub struct TouchEvent {
    pub x: f32,
    pub y: f32,
    pub action: TouchAction,
    pub pointer_id: i32,
    pub timestamp: f64,
}

/// Sensor types matching Android Sensor class
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SensorType {
    Accelerometer = 1,
    Gyroscope = 4,
    Magnetometer = 2,
    Gravity = 9,
    LinearAcceleration = 10,
    RotationVector = 11,
}

impl From<i32> for SensorType {
    fn from(value: i32) -> Self {
        match value {
            1 => SensorType::Accelerometer,
            4 => SensorType::Gyroscope,
            2 => SensorType::Magnetometer,
            9 => SensorType::Gravity,
            10 => SensorType::LinearAcceleration,
            11 => SensorType::RotationVector,
            _ => SensorType::Accelerometer,
        }
    }
}

/// Sensor event data
#[derive(Debug, Clone)]
pub struct SensorEvent {
    pub sensor_type: SensorType,
    pub values: Vec<f32>,
    pub timestamp: f64,
}

/// Android Intent data
#[derive(Debug, Clone)]
pub struct IntentData {
    pub action: String,
    pub data: Option<String>,
    pub extras: Vec<(String, String)>,
}

/// Event queue for thread-safe event passing
#[derive(Debug)]
struct EventQueue {
    touch_events: VecDeque<TouchEvent>,
    sensor_events: VecDeque<SensorEvent>,
    intent_events: VecDeque<IntentData>,
}

impl EventQueue {
    fn new() -> Self {
        Self {
            touch_events: VecDeque::with_capacity(100),
            sensor_events: VecDeque::with_capacity(100),
            intent_events: VecDeque::with_capacity(10),
        }
    }

    fn push_touch(&mut self, event: TouchEvent) {
        if self.touch_events.len() >= MAX_EVENT_QUEUE_SIZE {
            self.touch_events.pop_front();
        }
        self.touch_events.push_back(event);
    }

    fn push_sensor(&mut self, event: SensorEvent) {
        if self.sensor_events.len() >= MAX_EVENT_QUEUE_SIZE {
            self.sensor_events.pop_front();
        }
        self.sensor_events.push_back(event);
    }

    fn push_intent(&mut self, data: IntentData) {
        if self.intent_events.len() >= MAX_EVENT_QUEUE_SIZE {
            self.intent_events.pop_front();
        }
        self.intent_events.push_back(data);
    }
}

/// Global event queue
static mut EVENT_QUEUE: Option<Arc<Mutex<EventQueue>>> = None;
static QUEUE_INIT: std::sync::Once = std::sync::Once::new();

/// Event bridge for Android events to Bevy
pub struct EventBridge;

impl EventBridge {
    /// Initialize the event bridge
    pub fn init() {
        QUEUE_INIT.call_once(|| {
            unsafe {
                EVENT_QUEUE = Some(Arc::new(Mutex::new(EventQueue::new())));
            }
        });
    }

    /// Send touch event from Android
    pub fn send_touch_event(x: f32, y: f32, action: i32, pointer_id: i32) -> Result<(), JniError> {
        Self::init();
        
        let event = TouchEvent {
            x,
            y,
            action: TouchAction::from(action),
            pointer_id,
            timestamp: Self::get_timestamp(),
        };

        unsafe {
            if let Some(queue) = &EVENT_QUEUE {
                let mut queue_guard = queue.lock()
                    .map_err(|e| JniError::ThreadError(e.to_string()))?;
                queue_guard.push_touch(event);
            }
        }

        Ok(())
    }

    /// Send sensor data from Android
    pub fn send_sensor_data(sensor_type: i32, values: Vec<f32>) -> Result<(), JniError> {
        Self::init();
        
        let event = SensorEvent {
            sensor_type: SensorType::from(sensor_type),
            values,
            timestamp: Self::get_timestamp(),
        };

        unsafe {
            if let Some(queue) = &EVENT_QUEUE {
                let mut queue_guard = queue.lock()
                    .map_err(|e| JniError::ThreadError(e.to_string()))?;
                queue_guard.push_sensor(event);
            }
        }

        Ok(())
    }

    /// Send Android Intent data
    pub fn send_intent(action: String, data: Option<String>, extras: Vec<(String, String)>) -> Result<(), JniError> {
        Self::init();
        
        let intent_data = IntentData {
            action,
            data,
            extras,
        };

        unsafe {
            if let Some(queue) = &EVENT_QUEUE {
                let mut queue_guard = queue.lock()
                    .map_err(|e| JniError::ThreadError(e.to_string()))?;
                queue_guard.push_intent(intent_data);
            }
        }

        Ok(())
    }

    /// Poll touch events (called from Bevy system)
    pub fn poll_touch_events() -> Vec<TouchEvent> {
        unsafe {
            if let Some(queue) = &EVENT_QUEUE {
                if let Ok(mut queue_guard) = queue.lock() {
                    return queue_guard.touch_events.drain(..).collect();
                }
            }
        }
        Vec::new()
    }

    /// Poll sensor events (called from Bevy system)
    pub fn poll_sensor_events() -> Vec<SensorEvent> {
        unsafe {
            if let Some(queue) = &EVENT_QUEUE {
                if let Ok(mut queue_guard) = queue.lock() {
                    return queue_guard.sensor_events.drain(..).collect();
                }
            }
        }
        Vec::new()
    }

    /// Poll intent events (called from Bevy system)
    pub fn poll_intent_events() -> Vec<IntentData> {
        unsafe {
            if let Some(queue) = &EVENT_QUEUE {
                if let Ok(mut queue_guard) = queue.lock() {
                    return queue_guard.intent_events.drain(..).collect();
                }
            }
        }
        Vec::new()
    }

    /// Get current timestamp in seconds
    fn get_timestamp() -> f64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs_f64()
    }
}

/// Bevy plugin for Android event handling
pub struct AndroidEventPlugin;

impl Plugin for AndroidEventPlugin {
    fn build(&self, app: &mut App) {
        app.add_systems(Update, (
            process_touch_events,
            process_sensor_events,
            process_intent_events,
        ));
        
        // Add event types
        app.add_event::<AndroidTouchEvent>();
        app.add_event::<AndroidSensorEvent>();
        app.add_event::<AndroidIntentEvent>();
    }
}

/// Bevy event for Android touch
#[derive(Event, Debug, Clone)]
pub struct AndroidTouchEvent {
    pub position: Vec2,
    pub action: TouchAction,
    pub pointer_id: i32,
}

/// Bevy event for Android sensor
#[derive(Event, Debug, Clone)]
pub struct AndroidSensorEvent {
    pub sensor_type: SensorType,
    pub values: Vec<f32>,
}

/// Bevy event for Android intent
#[derive(Event, Debug, Clone)]
pub struct AndroidIntentEvent {
    pub action: String,
    pub data: Option<String>,
    pub extras: Vec<(String, String)>,
}

/// System to process touch events
fn process_touch_events(mut events: EventWriter<AndroidTouchEvent>) {
    for touch in EventBridge::poll_touch_events() {
        events.send(AndroidTouchEvent {
            position: Vec2::new(touch.x, touch.y),
            action: touch.action,
            pointer_id: touch.pointer_id,
        });
    }
}

/// System to process sensor events
fn process_sensor_events(mut events: EventWriter<AndroidSensorEvent>) {
    for sensor in EventBridge::poll_sensor_events() {
        events.send(AndroidSensorEvent {
            sensor_type: sensor.sensor_type,
            values: sensor.values,
        });
    }
}

/// System to process intent events
fn process_intent_events(mut events: EventWriter<AndroidIntentEvent>) {
    for intent in EventBridge::poll_intent_events() {
        events.send(AndroidIntentEvent {
            action: intent.action,
            data: intent.data,
            extras: intent.extras,
        });
    }
}