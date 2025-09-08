use bevy::prelude::*;
use std::collections::VecDeque;

/// Pattern Echo System - Record and replay pattern transformations
/// 
/// This mechanic allows players to "record" a sequence of transformations
/// and then "echo" them onto new patterns, creating complex solutions
/// from simple building blocks - directly training ARC reasoning skills.
pub struct PatternEchoPlugin;

impl Plugin for PatternEchoPlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(EchoRecorder::default())
            .insert_resource(PatternLibrary::default())
            .add_event::<EchoPlaybackEvent>()
            .add_systems(Update, (
                record_transformations,
                playback_echo,
                combine_echoes,
                validate_arc_solution,
            ).chain());
    }
}

/// A transformation that can be recorded and replayed
#[derive(Clone, Debug)]
pub enum Transformation {
    // Basic ARC transformations
    Rotate { angle: f32 },
    Mirror { axis: Axis },
    Translate { delta: Vec2 },
    Scale { factor: f32 },
    ColorShift { hue_delta: f32 },
    
    // Advanced transformations
    Duplicate { offset: Vec2, count: usize },
    Filter { predicate: FilterType },
    Compose { transforms: Vec<Transformation> },
    Conditional { condition: Condition, then_transform: Box<Transformation> },
    
    // Meta transformations (for type theory)
    Lift { dimension: usize },
    Project { dimension: usize },
    Homotopy { path: Vec<Vec2> },
}

#[derive(Clone, Debug)]
pub enum FilterType {
    ByColor(Color),
    BySize(f32, f32), // min, max
    ByShape(ShapeType),
    ByPosition(Vec2, f32), // center, radius
}

#[derive(Clone, Debug)]
pub enum ShapeType {
    Square,
    Circle,
    Triangle,
    Custom(Vec<Vec2>),
}

#[derive(Clone, Debug)]
pub enum Condition {
    HasColor(Color),
    TouchingEdge,
    NearPattern(PatternId),
    CountGreaterThan(usize),
}

#[derive(Clone, Debug)]
pub enum Axis {
    Horizontal,
    Vertical,
    Diagonal,
}

/// Records player transformations
#[derive(Resource, Default)]
pub struct EchoRecorder {
    pub recording: bool,
    pub current_sequence: VecDeque<RecordedTransform>,
    pub saved_echoes: Vec<Echo>,
    pub max_sequence_length: usize,
}

#[derive(Clone, Debug)]
pub struct RecordedTransform {
    pub transformation: Transformation,
    pub timestamp: f32,
    pub source_pattern: Option<PatternId>,
    pub result_pattern: Option<PatternId>,
}

/// A saved echo that can be replayed
#[derive(Clone, Debug)]
pub struct Echo {
    pub id: EchoId,
    pub name: String,
    pub sequence: Vec<RecordedTransform>,
    pub complexity: f32,
    pub times_used: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct EchoId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PatternId(pub u32);

/// Library of discovered patterns
#[derive(Resource, Default)]
pub struct PatternLibrary {
    pub patterns: Vec<Pattern>,
    pub arc_challenges: Vec<ARCChallenge>,
    pub discovered_rules: Vec<TransformationRule>,
}

#[derive(Clone, Debug)]
pub struct Pattern {
    pub id: PatternId,
    pub cells: Vec<Vec<CellState>>,
    pub metadata: PatternMetadata,
}

#[derive(Clone, Debug)]
pub struct CellState {
    pub color: Color,
    pub symbol: Option<char>,
    pub active: bool,
}

#[derive(Clone, Debug)]
pub struct PatternMetadata {
    pub symmetry: Symmetry,
    pub complexity: f32,
    pub category: PatternCategory,
}

#[derive(Clone, Debug)]
pub enum Symmetry {
    None,
    Horizontal,
    Vertical,
    Rotational(u8), // n-fold symmetry
    Full,
}

#[derive(Clone, Debug)]
pub enum PatternCategory {
    Geometric,
    Organic,
    Abstract,
    Mathematical,
}

/// ARC-style challenge
#[derive(Clone, Debug)]
pub struct ARCChallenge {
    pub id: u32,
    pub input_patterns: Vec<Pattern>,
    pub output_patterns: Vec<Pattern>,
    pub hidden_rule: TransformationRule,
    pub difficulty: f32,
    pub solved: bool,
}

#[derive(Clone, Debug)]
pub struct TransformationRule {
    pub description: String,
    pub transformations: Vec<Transformation>,
    pub is_compositional: bool,
}

/// Event for echo playback
#[derive(Event)]
pub struct EchoPlaybackEvent {
    pub echo_id: EchoId,
    pub target_pattern: PatternId,
    pub playback_speed: f32,
}

/// Component for entities with active echoes
#[derive(Component)]
pub struct ActiveEcho {
    pub echo: Echo,
    pub current_step: usize,
    pub timer: Timer,
    pub target_entities: Vec<Entity>,
}

/// Record player transformations
fn record_transformations(
    mut recorder: ResMut<EchoRecorder>,
    keyboard: Res<ButtonInput<KeyCode>>,
    time: Res<Time>,
    pattern_query: Query<&Pattern>,
) {
    // Toggle recording with R key
    if keyboard.just_pressed(KeyCode::KeyR) {
        recorder.recording = !recorder.recording;
        
        if recorder.recording {
            info!("Echo recording started");
            recorder.current_sequence.clear();
        } else if !recorder.current_sequence.is_empty() {
            // Save the echo
            let echo = Echo {
                id: EchoId(recorder.saved_echoes.len() as u32),
                name: format!("Echo #{}", recorder.saved_echoes.len() + 1),
                sequence: recorder.current_sequence.clone().into(),
                complexity: calculate_complexity(&recorder.current_sequence),
                times_used: 0,
            };
            recorder.saved_echoes.push(echo);
            info!("Echo saved with {} transformations", recorder.current_sequence.len());
        }
    }
    
    // Record transformations based on input
    if recorder.recording {
        if keyboard.just_pressed(KeyCode::KeyQ) {
            recorder.current_sequence.push_back(RecordedTransform {
                transformation: Transformation::Rotate { angle: 90.0 },
                timestamp: time.elapsed_secs(),
                source_pattern: None,
                result_pattern: None,
            });
        }
        
        if keyboard.just_pressed(KeyCode::KeyM) {
            recorder.current_sequence.push_back(RecordedTransform {
                transformation: Transformation::Mirror { axis: Axis::Horizontal },
                timestamp: time.elapsed_secs(),
                source_pattern: None,
                result_pattern: None,
            });
        }
        
        // Limit sequence length
        while recorder.current_sequence.len() > recorder.max_sequence_length {
            recorder.current_sequence.pop_front();
        }
    }
}

/// Playback recorded echoes
fn playback_echo(
    mut commands: Commands,
    mut playback_events: EventReader<EchoPlaybackEvent>,
    recorder: Res<EchoRecorder>,
    mut pattern_query: Query<&mut Pattern>,
) {
    for event in playback_events.read() {
        if let Some(echo) = recorder.saved_echoes.iter().find(|e| e.id == event.echo_id) {
            // Create active echo component
            commands.spawn(ActiveEcho {
                echo: echo.clone(),
                current_step: 0,
                timer: Timer::from_seconds(1.0 / event.playback_speed, TimerMode::Repeating),
                target_entities: vec![], // Would collect target entities
            });
            
            info!("Starting echo playback: {}", echo.name);
        }
    }
}

/// Combine multiple echoes into complex transformations
fn combine_echoes(
    mut recorder: ResMut<EchoRecorder>,
    keyboard: Res<ButtonInput<KeyCode>>,
) {
    if keyboard.just_pressed(KeyCode::KeyC) && recorder.saved_echoes.len() >= 2 {
        // Combine last two echoes
        let len = recorder.saved_echoes.len();
        let echo1 = recorder.saved_echoes[len - 2].clone();
        let echo2 = recorder.saved_echoes[len - 1].clone();
        
        let mut combined_sequence = echo1.sequence.clone();
        combined_sequence.extend(echo2.sequence);
        
        let combined_echo = Echo {
            id: EchoId(len as u32),
            name: format!("{} + {}", echo1.name, echo2.name),
            sequence: combined_sequence,
            complexity: echo1.complexity + echo2.complexity * 0.8,
            times_used: 0,
        };
        
        recorder.saved_echoes.push(combined_echo);
        info!("Created combined echo");
    }
}

/// Validate if transformation solves ARC puzzle
fn validate_arc_solution(
    mut library: ResMut<PatternLibrary>,
    active_echoes: Query<&ActiveEcho>,
) {
    for echo in active_echoes.iter() {
        // Check if echo solves any ARC challenges
        for challenge in &mut library.arc_challenges {
            if !challenge.solved && echo_solves_challenge(echo, challenge) {
                challenge.solved = true;
                info!("ARC Challenge {} solved using echo!", challenge.id);
                
                // Learn the rule
                library.discovered_rules.push(challenge.hidden_rule.clone());
            }
        }
    }
}

// Helper functions
fn calculate_complexity(sequence: &VecDeque<RecordedTransform>) -> f32 {
    sequence.len() as f32 * 0.5 + count_unique_transforms(sequence) as f32 * 0.3
}

fn count_unique_transforms(sequence: &VecDeque<RecordedTransform>) -> usize {
    // Simplified - would check for unique transformation types
    sequence.len()
}

fn echo_solves_challenge(echo: &ActiveEcho, challenge: &ARCChallenge) -> bool {
    // Simplified validation - would apply echo to input and check against output
    false
}