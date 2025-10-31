use bevy::prelude::*;
use std::collections::{HashMap, VecDeque};
use std::time::Instant;

/// Enhanced Type Theory Visualization with Debug Mode
/// 
/// This module extends the type theory visualization to provide powerful
/// debugging capabilities for both gameplay mechanics and engine internals.
/// It can inspect ECS components, track system performance, and visualize
/// game state as mathematical structures.

pub struct TypeTheoryDebugPlugin;

impl Plugin for TypeTheoryDebugPlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(DebugContext::default())
            .insert_resource(PerformanceProfiler::default())
            .insert_resource(TypeInspector::default())
            .add_state::<DebugMode>()
            .add_event::<DebugEvent>()
            .add_systems(Update, (
                toggle_debug_mode,
                update_performance_metrics,
                inspect_entity_types,
                visualize_system_graph,
                render_debug_overlay,
                handle_debug_commands,
            ).chain());
    }
}

/// Debug modes for different inspection needs
#[derive(States, Default, Debug, Clone, PartialEq, Eq, Hash)]
pub enum DebugMode {
    #[default]
    Off,
    EntityInspector,    // Inspect ECS entities and components
    SystemProfiler,     // Profile system performance
    TypeChecker,        // Validate type constraints
    MemoryAnalyzer,     // Memory usage visualization
    NetworkDebugger,    // Network state inspection
    AIReasoning,        // Visualize AI decision trees
}

/// Core debug context
#[derive(Resource)]
pub struct DebugContext {
    pub enabled: bool,
    pub verbosity: DebugVerbosity,
    pub selected_entity: Option<Entity>,
    pub breakpoints: Vec<Breakpoint>,
    pub watch_list: HashMap<String, WatchTarget>,
    pub history: VecDeque<DebugSnapshot>,
    pub overlay_config: OverlayConfig,
}

impl Default for DebugContext {
    fn default() -> Self {
        Self {
            enabled: false,
            verbosity: DebugVerbosity::Normal,
            selected_entity: None,
            breakpoints: Vec::new(),
            watch_list: HashMap::new(),
            history: VecDeque::with_capacity(500), // Reduced capacity for memory efficiency
            overlay_config: OverlayConfig::default(),
        }
    }
}

impl DebugContext {
    /// Maximum number of history entries to keep
    const MAX_HISTORY: usize = 500;
    const MAX_WATCHES: usize = 100;
    const MAX_BREAKPOINTS: usize = 50;
    
    /// Clean up old history entries to prevent memory leaks
    pub fn cleanup_history(&mut self) {
        while self.history.len() > Self::MAX_HISTORY {
            self.history.pop_front();
        }
    }
    
    /// Add a watch target with bounds checking
    pub fn add_watch(&mut self, name: String, target: WatchTarget) -> Result<(), String> {
        if self.watch_list.len() >= Self::MAX_WATCHES {
            return Err("Maximum number of watch targets exceeded".to_string());
        }
        self.watch_list.insert(name, target);
        Ok(())
    }
    
    /// Add a breakpoint with bounds checking
    pub fn add_breakpoint(&mut self, breakpoint: Breakpoint) -> Result<(), String> {
        if self.breakpoints.len() >= Self::MAX_BREAKPOINTS {
            return Err("Maximum number of breakpoints exceeded".to_string());
        }
        self.breakpoints.push(breakpoint);
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
pub enum DebugVerbosity {
    Minimal,
    Normal,
    Verbose,
    Trace,
}

/// Breakpoint system for debugging game logic
#[derive(Clone)]
pub struct Breakpoint {
    pub id: BreakpointId,
    pub condition: BreakpointCondition,
    pub enabled: bool,
    pub hit_count: usize,
    pub action: BreakpointAction,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BreakpointId(pub u32);

#[derive(Clone)]
pub enum BreakpointCondition {
    EntitySpawned(ComponentFilter),
    ComponentChanged(ComponentFilter),
    ResourceModified(String),
    SystemExecuted(String),
    FrameNumber(u64),
    // Custom breakpoints removed for security - use predefined conditions instead
}

#[derive(Clone)]
pub struct ComponentFilter {
    pub type_name: String,
    pub predicate: Option<String>, // Serialized predicate
}

#[derive(Clone)]
pub enum BreakpointAction {
    Pause,
    Log(String),
    TakeSnapshot,
    ExecuteCommand(String),
}

/// Watch targets for real-time monitoring
#[derive(Clone)]
pub enum WatchTarget {
    Entity(Entity),
    Component(Entity, String),
    Resource(String),
    Query(String), // Query DSL
    Performance(MetricType),
}

#[derive(Clone)]
pub enum MetricType {
    FPS,
    SystemTime(String),
    MemoryUsage,
    EntityCount,
    DrawCalls,
}

/// Debug snapshot for time-travel debugging
#[derive(Clone)]
pub struct DebugSnapshot {
    pub timestamp: Instant,
    pub frame: u64,
    pub entities: Vec<EntitySnapshot>,
    pub resources: HashMap<String, ResourceSnapshot>,
    pub metrics: PerformanceMetrics,
}

#[derive(Clone)]
pub struct EntitySnapshot {
    pub entity: Entity,
    pub components: HashMap<String, ComponentData>,
    pub relationships: Vec<(Entity, RelationType)>,
}

#[derive(Clone)]
pub struct ComponentData {
    pub type_name: String,
    pub size: usize,
    pub data: Vec<u8>, // Serialized component
    pub visualization: Option<TypeVisualization>,
}

#[derive(Clone)]
pub enum RelationType {
    Parent,
    Child,
    Reference(String),
}

#[derive(Clone)]
pub struct ResourceSnapshot {
    pub type_name: String,
    pub size: usize,
    pub data: Vec<u8>,
}

/// Performance profiler
#[derive(Resource)]
pub struct PerformanceProfiler {
    pub frame_times: VecDeque<f32>,
    pub system_times: HashMap<String, VecDeque<f32>>,
    pub memory_samples: VecDeque<MemorySample>,
    pub hotspots: Vec<Hotspot>,
    pub recording: bool,
}

impl Default for PerformanceProfiler {
    fn default() -> Self {
        Self {
            frame_times: VecDeque::with_capacity(120),
            system_times: HashMap::new(),
            memory_samples: VecDeque::with_capacity(60),
            hotspots: Vec::new(),
            recording: false,
        }
    }
}

impl PerformanceProfiler {
    /// Maximum number of frame times to keep
    const MAX_FRAME_TIMES: usize = 120;
    const MAX_MEMORY_SAMPLES: usize = 60;
    const MAX_SYSTEM_SAMPLES: usize = 120;
    const MAX_SYSTEMS: usize = 100;
    
    /// Add a frame time with automatic cleanup
    pub fn add_frame_time(&mut self, frame_time: f32) {
        self.frame_times.push_back(frame_time);
        while self.frame_times.len() > Self::MAX_FRAME_TIMES {
            self.frame_times.pop_front();
        }
    }
    
    /// Add a system time sample with automatic cleanup
    pub fn add_system_time(&mut self, system_name: String, time: f32) -> Result<(), String> {
        if self.system_times.len() >= Self::MAX_SYSTEMS && !self.system_times.contains_key(&system_name) {
            return Err("Maximum number of tracked systems exceeded".to_string());
        }
        
        let times = self.system_times.entry(system_name).or_insert_with(|| VecDeque::with_capacity(Self::MAX_SYSTEM_SAMPLES));
        times.push_back(time);
        
        while times.len() > Self::MAX_SYSTEM_SAMPLES {
            times.pop_front();
        }
        Ok(())
    }
    
    /// Add a memory sample with automatic cleanup
    pub fn add_memory_sample(&mut self, sample: MemorySample) {
        self.memory_samples.push_back(sample);
        while self.memory_samples.len() > Self::MAX_MEMORY_SAMPLES {
            self.memory_samples.pop_front();
        }
    }
}

#[derive(Clone)]
pub struct MemorySample {
    pub timestamp: Instant,
    pub heap_usage: usize,
    pub entity_count: usize,
    pub component_pools: HashMap<String, usize>,
}

#[derive(Clone)]
pub struct Hotspot {
    pub system_name: String,
    pub average_time: f32,
    pub worst_time: f32,
    pub call_count: usize,
}

/// Type inspector for runtime type checking
#[derive(Resource, Default)]
pub struct TypeInspector {
    pub type_registry: HashMap<String, TypeInfo>,
    pub constraints: Vec<TypeConstraint>,
    pub violations: Vec<ConstraintViolation>,
}

#[derive(Clone)]
pub struct TypeInfo {
    pub name: String,
    pub size: usize,
    pub alignment: usize,
    pub fields: Vec<FieldInfo>,
    pub methods: Vec<MethodInfo>,
    pub traits: Vec<String>,
}

#[derive(Clone)]
pub struct FieldInfo {
    pub name: String,
    pub type_name: String,
    pub offset: usize,
    pub visibility: Visibility,
}

#[derive(Clone)]
pub enum Visibility {
    Public,
    Private,
    Protected,
}

#[derive(Clone)]
pub struct MethodInfo {
    pub name: String,
    pub signature: String,
    pub is_mutable: bool,
}

#[derive(Clone)]
pub struct TypeConstraint {
    pub name: String,
    pub predicate: ConstraintPredicate,
    pub severity: ConstraintSeverity,
}

#[derive(Clone)]
pub enum ConstraintPredicate {
    ComponentRequires(String, String), // Component A requires B
    ResourceExists(String),
    EntityHasComponents(Vec<String>),
    Custom(String), // Serialized predicate
}

#[derive(Clone, Copy)]
pub enum ConstraintSeverity {
    Warning,
    Error,
    Fatal,
}

#[derive(Clone)]
pub struct ConstraintViolation {
    pub constraint: TypeConstraint,
    pub entity: Option<Entity>,
    pub message: String,
    pub stack_trace: Vec<String>,
}

/// Overlay configuration
#[derive(Clone)]
pub struct OverlayConfig {
    pub show_fps: bool,
    pub show_entity_count: bool,
    pub show_system_graph: bool,
    pub show_memory_usage: bool,
    pub show_type_hints: bool,
    pub highlight_selected: bool,
    pub colors: DebugColors,
}

impl Default for OverlayConfig {
    fn default() -> Self {
        Self {
            show_fps: true,
            show_entity_count: true,
            show_system_graph: false,
            show_memory_usage: false,
            show_type_hints: true,
            highlight_selected: true,
            colors: DebugColors::default(),
        }
    }
}

#[derive(Clone)]
pub struct DebugColors {
    pub overlay_bg: Color,
    pub text: Color,
    pub warning: Color,
    pub error: Color,
    pub success: Color,
    pub highlight: Color,
}

impl Default for DebugColors {
    fn default() -> Self {
        Self {
            overlay_bg: Color::srgba(0.0, 0.0, 0.0, 0.8),
            text: Color::srgb(0.9, 0.9, 0.9),
            warning: Color::srgb(1.0, 0.8, 0.0),
            error: Color::srgb(1.0, 0.2, 0.2),
            success: Color::srgb(0.2, 1.0, 0.2),
            highlight: Color::srgb(0.0, 0.8, 1.0),
        }
    }
}

/// Type visualization for debugging
#[derive(Clone)]
pub struct TypeVisualization {
    pub shape: DebugShape,
    pub color: Color,
    pub label: String,
    pub connections: Vec<ConnectionVisualization>,
}

#[derive(Clone)]
pub enum DebugShape {
    Box(Vec3),
    Sphere(f32),
    Arrow(Vec3, Vec3),
    Graph(Vec<Vec3>, Vec<(usize, usize)>),
    Text(String),
}

#[derive(Clone)]
pub struct ConnectionVisualization {
    pub target: Entity,
    pub connection_type: String,
    pub strength: f32,
}

/// Debug events
#[derive(Event)]
pub struct DebugEvent {
    pub event_type: DebugEventType,
    pub timestamp: Instant,
}

#[derive(Clone)]
pub enum DebugEventType {
    BreakpointHit(BreakpointId),
    ConstraintViolated(ConstraintViolation),
    PerformanceWarning(String),
    WatchTriggered(String, String), // Watch name, new value
    CommandExecuted(String),
}

/// Performance metrics
#[derive(Clone, Default)]
pub struct PerformanceMetrics {
    pub fps: f32,
    pub frame_time: f32,
    pub entity_count: usize,
    pub system_count: usize,
    pub draw_calls: usize,
    pub memory_usage: MemoryUsage,
}

#[derive(Clone, Default)]
pub struct MemoryUsage {
    pub heap: usize,
    pub components: usize,
    pub textures: usize,
    pub meshes: usize,
}

/// Toggle debug mode with F12
fn toggle_debug_mode(
    mut debug_context: ResMut<DebugContext>,
    keyboard: Res<ButtonInput<KeyCode>>,
    mut next_state: ResMut<NextState<DebugMode>>,
    current_state: Res<State<DebugMode>>,
) {
    if keyboard.just_pressed(KeyCode::F12) {
        debug_context.enabled = !debug_context.enabled;
        
        if debug_context.enabled {
            next_state.set(DebugMode::EntityInspector);
            info!("Debug mode enabled");
        } else {
            next_state.set(DebugMode::Off);
            info!("Debug mode disabled");
        }
    }
    
    // Cycle through debug modes with F11
    if keyboard.just_pressed(KeyCode::F11) && debug_context.enabled {
        let next = match current_state.get() {
            DebugMode::Off => DebugMode::EntityInspector,
            DebugMode::EntityInspector => DebugMode::SystemProfiler,
            DebugMode::SystemProfiler => DebugMode::TypeChecker,
            DebugMode::TypeChecker => DebugMode::MemoryAnalyzer,
            DebugMode::MemoryAnalyzer => DebugMode::NetworkDebugger,
            DebugMode::NetworkDebugger => DebugMode::AIReasoning,
            DebugMode::AIReasoning => DebugMode::EntityInspector,
        };
        next_state.set(next);
        info!("Switched to debug mode: {:?}", next);
    }
}

/// Update performance metrics
fn update_performance_metrics(
    mut profiler: ResMut<PerformanceProfiler>,
    time: Res<Time>,
    query: Query<Entity>,
) {
    if !profiler.recording {
        return;
    }
    
    let frame_time = time.delta_secs();
    profiler.add_frame_time(frame_time);
    
    // Update memory sample
    let sample = MemorySample {
        timestamp: Instant::now(),
        heap_usage: 0, // Would use actual memory API
        entity_count: query.iter().count(),
        component_pools: HashMap::new(),
    };
    
    profiler.add_memory_sample(sample);
}

/// Inspect entity types and components
fn inspect_entity_types(
    debug_context: Res<DebugContext>,
    mut inspector: ResMut<TypeInspector>,
    query: Query<Entity>,
    mut gizmos: Gizmos,
) {
    if !debug_context.enabled {
        return;
    }
    
    if let Some(selected) = debug_context.selected_entity {
        // Draw selection highlight
        gizmos.sphere(
            Isometry3d::from_translation(Vec3::ZERO),
            1.0,
            debug_context.overlay_config.colors.highlight,
        );
        
        // Would inspect actual components here
        info!("Inspecting entity: {:?}", selected);
    }
    
    // Check type constraints
    for constraint in &inspector.constraints {
        // Validate constraint
        // Record violations
    }
}

/// Visualize system execution graph
fn visualize_system_graph(
    debug_context: Res<DebugContext>,
    mut gizmos: Gizmos,
) {
    if !debug_context.enabled || !debug_context.overlay_config.show_system_graph {
        return;
    }
    
    // Would visualize actual system dependencies
    // Draw nodes for systems
    // Draw edges for dependencies
}

/// Render debug overlay UI
fn render_debug_overlay(
    debug_context: Res<DebugContext>,
    profiler: Res<PerformanceProfiler>,
    mut gizmos: Gizmos,
) {
    if !debug_context.enabled {
        return;
    }
    
    // Calculate average FPS
    let avg_fps = if !profiler.frame_times.is_empty() {
        let avg_time: f32 = profiler.frame_times.iter().sum::<f32>() / profiler.frame_times.len() as f32;
        1.0 / avg_time
    } else {
        0.0
    };
    
    // Draw FPS counter
    if debug_context.overlay_config.show_fps {
        // Would use actual UI rendering here
        gizmos.rect_2d(Vec2::new(-100.0, 100.0), 0.0, Vec2::new(200.0, 30.0), debug_context.overlay_config.colors.overlay_bg);
    }
    
    // Draw entity count
    if debug_context.overlay_config.show_entity_count {
        // Would display actual entity count
    }
}

/// Handle debug console commands
fn handle_debug_commands(
    mut debug_context: ResMut<DebugContext>,
    keyboard: Res<ButtonInput<KeyCode>>,
    mut commands: Commands,
) {
    if !debug_context.enabled {
        return;
    }
    
    // Pause/resume with P
    if keyboard.just_pressed(KeyCode::KeyP) {
        // Would pause game execution
        info!("Debug pause toggled");
    }
    
    // Take snapshot with S
    if keyboard.just_pressed(KeyCode::KeyS) {
        let snapshot = DebugSnapshot {
            timestamp: Instant::now(),
            frame: 0, // Would get actual frame number
            entities: Vec::new(),
            resources: HashMap::new(),
            metrics: PerformanceMetrics::default(),
        };
        
        debug_context.history.push_back(snapshot);
        debug_context.cleanup_history(); // Ensure we don't exceed limits
        info!("Debug snapshot taken (total: {})", debug_context.history.len());
    }
    
    // Clear debug info with C
    if keyboard.just_pressed(KeyCode::KeyC) {
        debug_context.history.clear();
        debug_context.watch_list.clear();
        debug_context.breakpoints.clear();
        info!("Debug info cleared");
    }
}

/// Helper trait for type debugging
pub trait TypeDebugExt {
    fn debug_shape(&self) -> DebugShape;
    fn debug_color(&self) -> Color;
    fn debug_label(&self) -> String;
}

/// Macro for adding debug watches with error handling
#[macro_export]
macro_rules! debug_watch {
    ($context:expr, $name:expr, $target:expr) => {
        match $context.add_watch($name.to_string(), $target) {
            Ok(_) => info!("Debug watch added: {}", $name),
            Err(e) => warn!("Failed to add debug watch '{}': {}", $name, e),
        }
    };
}

/// Macro for setting breakpoints with error handling
#[macro_export]
macro_rules! debug_break {
    ($context:expr, $condition:expr) => {
        let breakpoint = Breakpoint {
            id: BreakpointId($context.breakpoints.len() as u32),
            condition: $condition,
            enabled: true,
            hit_count: 0,
            action: BreakpointAction::Pause,
        };
        match $context.add_breakpoint(breakpoint) {
            Ok(_) => info!("Breakpoint added: {:?}", $condition),
            Err(e) => warn!("Failed to add breakpoint: {}", e),
        }
    };
}