/// Engine Creation and Management
/// 
/// This module handles the creation and lifecycle of the Bevy engine instance.

use super::*;
use bevy::prelude::*;
use bevy::window::{PresentMode, WindowTheme};
use bevy::asset::AssetMode;
use bevy::log::warn;
use std::sync::{Arc, Mutex};
use std::sync::atomic::AtomicBool;

/// Create a new engine instance with the given configuration
pub fn create_engine(
    config: EngineConfig,
    error_callback: ErrorCallback,
) -> Result<EngineHandle, String> {
    // Create the Bevy app
    let mut app = App::new();
    
    // Configure window settings based on iOS config
    let window_plugin = WindowPlugin {
        primary_window: Some(Window {
            title: "Runetika".to_string(),
            resolution: (config.window_width, config.window_height).into(),
            present_mode: if config.target_fps >= 120 {
                PresentMode::Immediate
            } else {
                PresentMode::AutoVsync
            },
            window_theme: Some(WindowTheme::Dark),
            decorations: false,  // No decorations on iOS
            resizable: false,    // iOS windows aren't resizable
            ..default()
        }),
        ..default()
    };
    
    // Add default plugins with iOS-specific configuration
    app.add_plugins(
        DefaultPlugins
            .set(window_plugin)
            .set(ImagePlugin::default_nearest())
            // Disable file asset loading on iOS - use embedded assets
            .set(AssetPlugin {
                mode: AssetMode::Processed,
                ..default()
            })
    );
    
    // Initialize game state
    app.init_state::<crate::GameState>();
    
    // Add game plugins
    app.add_plugins((
        crate::menu::MainMenuPlugin,
        crate::settings::SettingsPlugin,
        crate::credits::CreditsPlugin,
        crate::silicon_mind::SiliconMindPlugin,
        crate::terminal_interface::TerminalInterfacePlugin,
        crate::arc_engine::ARCEnginePlugin,
        crate::papilio::PapilioPlugin,
    ));
    
    // Add iOS-specific systems
    app.add_plugins(IOSPlugin {
        config: config.clone(),
    });
    
    // Create the engine handle
    let handle = EngineHandle {
        app: Arc::new(Mutex::new(app)),
        event_queue: Arc::new(Mutex::new(Vec::new())),
        callbacks: Arc::new(Mutex::new(CallbackRegistry {
            error_callback,
            log_callback: None,
            frame_callback: None,
            event_callback: None,
        })),
        render_thread: None,
        should_shutdown: Arc::new(AtomicBool::new(false)),
    };
    
    Ok(handle)
}

/// iOS-specific plugin for handling platform integration
struct IOSPlugin {
    config: EngineConfig,
}

impl Plugin for IOSPlugin {
    fn build(&self, app: &mut App) {
        // Add iOS event resources
        app.insert_resource(IOSConfig {
            scale_factor: self.config.scale_factor,
            max_touches: self.config.max_touches,
            use_metal: self.config.use_metal,
        });
        
        // Add iOS event queue
        app.insert_resource(IOSEventQueue::default());
        
        // Add performance monitoring if enabled
        if self.config.enable_profiling {
            app.insert_resource(PerformanceMonitor::default());
            app.add_systems(Update, update_performance_metrics);
        }
        
        // Add iOS input systems
        app.add_systems(PreUpdate, (
            process_ios_touch_events,
            process_ios_motion_events,
            process_ios_lifecycle_events,
        ));
        
        // Add debug rendering if enabled
        if self.config.debug_mode {
            app.add_systems(PostUpdate, debug_render_system);
        }
    }
}

/// iOS configuration resource
#[derive(Resource)]
struct IOSConfig {
    scale_factor: f32,
    max_touches: u32,
    use_metal: bool,
}

/// iOS event queue resource
#[derive(Resource, Default)]
struct IOSEventQueue {
    events: Arc<Mutex<Vec<IOSEvent>>>,
}

/// Performance monitoring resource
#[derive(Resource, Default)]
struct PerformanceMonitor {
    frame_count: u32,
    total_frame_time: f32,
    last_fps_update: std::time::Instant,
    current_fps: f32,
    metrics: PerformanceMetrics,
}

/// Process iOS touch events and convert to Bevy input events
fn process_ios_touch_events(
    mut touch_events: EventWriter<bevy::input::touch::TouchInput>,
    ios_queue: Res<IOSEventQueue>,
    config: Res<IOSConfig>,
) {
    if let Ok(mut events) = ios_queue.events.lock() {
        events.retain(|event| {
            if let IOSEvent::Touch(touch) = event {
                // Convert iOS touch to Bevy touch event
                let bevy_phase = match touch.phase {
                    TouchPhase::Began => bevy::input::touch::TouchPhase::Started,
                    TouchPhase::Moved => bevy::input::touch::TouchPhase::Moved,
                    TouchPhase::Stationary => bevy::input::touch::TouchPhase::Moved,
                    TouchPhase::Ended => bevy::input::touch::TouchPhase::Ended,
                    TouchPhase::Cancelled => bevy::input::touch::TouchPhase::Canceled,
                };
                
                touch_events.send(bevy::input::touch::TouchInput {
                    phase: bevy_phase,
                    position: Vec2::new(
                        touch.position.0 * config.scale_factor,
                        touch.position.1 * config.scale_factor,
                    ),
                    window: Entity::PLACEHOLDER,  // Will be filled by Bevy
                    force: Some(bevy::input::touch::ForceTouch::Normalized(touch.force as f64)),
                    id: touch.id,
                });
                
                false  // Remove from queue
            } else {
                true  // Keep in queue
            }
        });
    }
}

/// Process iOS motion events (accelerometer, gyroscope)
fn process_ios_motion_events(
    ios_queue: Res<IOSEventQueue>,
    mut commands: Commands,
) {
    if let Ok(mut events) = ios_queue.events.lock() {
        events.retain(|event| {
            match event {
                IOSEvent::Accelerometer(accel) => {
                    // Send accelerometer event to game systems
                    commands.trigger(MotionEvent::Accelerometer {
                        x: accel.acceleration.0,
                        y: accel.acceleration.1,
                        z: accel.acceleration.2,
                    });
                    false
                }
                IOSEvent::Gyroscope(gyro) => {
                    // Send gyroscope event to game systems
                    commands.trigger(MotionEvent::Gyroscope {
                        x: gyro.rotation_rate.0,
                        y: gyro.rotation_rate.1,
                        z: gyro.rotation_rate.2,
                    });
                    false
                }
                IOSEvent::Orientation(orientation) => {
                    // Handle orientation changes
                    commands.trigger(OrientationChanged(*orientation));
                    false
                }
                _ => true,
            }
        });
    }
}

/// Process iOS lifecycle events
fn process_ios_lifecycle_events(
    ios_queue: Res<IOSEventQueue>,
    mut app_state: ResMut<NextState<crate::GameState>>,
) {
    if let Ok(mut events) = ios_queue.events.lock() {
        events.retain(|event| {
            if let IOSEvent::Lifecycle(lifecycle) = event {
                match lifecycle {
                    LifecycleEvent::WillResignActive | 
                    LifecycleEvent::DidEnterBackground => {
                        // Pause the game when app goes to background
                        // Save game state here
                        false
                    }
                    LifecycleEvent::DidBecomeActive => {
                        // Resume the game when app becomes active
                        false
                    }
                    LifecycleEvent::MemoryWarning => {
                        // Free up memory - unload unused assets
                        warn!("iOS memory warning received");
                        false
                    }
                    LifecycleEvent::WillTerminate => {
                        // Save critical data before termination
                        false
                    }
                    _ => false,
                }
            } else {
                true
            }
        });
    }
}

/// Update performance metrics
fn update_performance_metrics(
    mut monitor: ResMut<PerformanceMonitor>,
    time: Res<Time>,
    diagnostics: Res<bevy::diagnostic::DiagnosticsStore>,
) {
    monitor.frame_count += 1;
    monitor.total_frame_time += time.delta_seconds();
    
    // Update FPS every second
    if monitor.last_fps_update.elapsed().as_secs_f32() >= 1.0 {
        monitor.current_fps = monitor.frame_count as f32 / monitor.total_frame_time;
        monitor.metrics.fps = monitor.current_fps;
        monitor.metrics.frame_time_ms = 1000.0 / monitor.current_fps;
        
        // Reset counters
        monitor.frame_count = 0;
        monitor.total_frame_time = 0.0;
        monitor.last_fps_update = std::time::Instant::now();
    }
    
    // Update diagnostics
    if let Some(fps_diagnostic) = diagnostics.get(&bevy::diagnostic::FrameTimeDiagnosticsPlugin::FPS) {
        if let Some(fps) = fps_diagnostic.smoothed() {
            monitor.metrics.fps = fps as f32;
        }
    }
}

/// Debug rendering system for development
fn debug_render_system(
    mut gizmos: Gizmos,
    touches: Res<bevy::input::touch::Touches>,
) {
    // Draw touch points
    for touch in touches.iter() {
        gizmos.circle_2d(touch.position(), 20.0, Color::srgb(1.0, 0.0, 0.0));
    }
}

/// Custom events for iOS integration
#[derive(Event)]
enum MotionEvent {
    Accelerometer { x: f32, y: f32, z: f32 },
    Gyroscope { x: f32, y: f32, z: f32 },
}

#[derive(Event)]
struct OrientationChanged(DeviceOrientation);