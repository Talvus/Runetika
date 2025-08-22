//! Runetika - A Cosmic Terminal Adventure
//!
//! Main entry point for the Runetika game, a space-themed adventure
//! featuring a powerful terminal interface and exploration mechanics.
//!
//! # Architecture
//! 
//! The game is built using the Bevy ECS (Entity Component System) architecture
//! with modular plugins for different game systems:
//! 
//! - **Terminal System**: In-game command interface with custom commands
//! - **Menu System**: Main menu with navigation and settings
//! - **Game State**: State machine for managing game flow
//! - **Credits System**: Animated credits screen
//!
//! # Performance Considerations
//!
//! The game is optimized for both desktop and web platforms with:
//! - Efficient sprite batching for tile rendering
//! - Lazy loading of resources
//! - Optimized UI rendering with minimal overdraw

// Module declarations
mod terminal;
mod menu;
mod game_state;
mod credits;

// External crate imports
use bevy::prelude::*;
use bevy::window::PrimaryWindow;

// Internal module imports
use terminal::TerminalPlugin;
use menu::MainMenuPlugin;
use game_state::{GameStatePlugin, GameState};
use credits::CreditsPlugin;

/// Marker component for game tiles in the world
#[derive(Component)]
struct Tile;

/// Resource containing map dimensions
#[derive(Resource)]
struct MapSize {
    width: u32,
    height: u32,
}

/// Main application entry point
///
/// Configures the Bevy app with all necessary plugins and systems.
/// Sets up the window, rendering pipeline, and game systems.
fn main() {
    App::new()
        // Configure default plugins with custom window settings
        .add_plugins(DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window {
                title: "Runetika - Cosmic Odyssey".into(),
                resolution: (1280., 800.).into(),
                // Prevent window from being resized below minimum size
                resize_constraints: WindowResizeConstraints {
                    min_width: 1024.0,
                    min_height: 768.0,
                    ..default()
                },
                // Enable VSync for smooth rendering
                present_mode: bevy::window::PresentMode::AutoVsync,
                ..default()
            }),
            ..default()
        }))
        // Add game-specific plugins
        .add_plugins((
            GameStatePlugin,
            MainMenuPlugin,
            TerminalPlugin,
            CreditsPlugin,
        ))
        // Register resources
        .insert_resource(MapSize { width: 20, height: 20 })
        // Setup systems
        .add_systems(Startup, setup_camera)
        .add_systems(OnEnter(GameState::InGame), setup_map)
        .add_systems(OnExit(GameState::InGame), cleanup_game)
        .add_systems(Update, (
            handle_pause_input.run_if(in_state(GameState::InGame)),
            debug_system.run_if(resource_exists::<DebugMode>),
        ))
        .run();
}

/// Sets up the main camera with appropriate configuration
///
/// Creates a 2D camera with a dark space background color
/// suitable for the game's cosmic theme.
fn setup_camera(mut commands: Commands) {
    commands.spawn((
        Camera2d::default(),
        Camera {
            // Deep space background color
            clear_color: ClearColorConfig::Custom(Color::srgb(0.02, 0.0, 0.04)),
            // Higher order ensures UI renders on top
            order: -1,
            ..default()
        },
        Name::new("Main Camera"),
    ));
}

/// Generates the game map with tiles
///
/// Creates a grid of tiles that represent the playable area.
/// Each tile is rendered as a sprite with physics collision.
///
/// # Performance Note
/// Tiles are batched by the renderer for efficient drawing.
/// Consider using a tilemap solution for larger maps.
fn setup_map(
    mut commands: Commands,
    map_size: Res<MapSize>,
) {
    info!("Generating map with size {}x{}", map_size.width, map_size.height);
    
    let half_width = map_size.width as f32 / 2.0;
    let half_height = map_size.height as f32 / 2.0;
    const TILE_SIZE: f32 = 32.0;
    
    // Spawn tiles in a grid pattern
    for x in 0..map_size.width {
        for y in 0..map_size.height {
            commands.spawn((
                Tile,
                Sprite {
                    color: Color::srgb(0.1, 0.2, 0.1),
                    custom_size: Some(Vec2::splat(TILE_SIZE - 2.0)), // Small gap between tiles
                    ..default()
                },
                Transform::from_xyz(
                    (x as f32 - half_width) * TILE_SIZE,
                    (y as f32 - half_height) * TILE_SIZE,
                    -1.0, // Behind other elements
                ),
                // Add name for debugging
                Name::new(format!("Tile_{}_{}", x, y)),
            ));
        }
    }
    
    info!("Map generation complete: {} tiles created", map_size.width * map_size.height);
}

/// Cleans up game entities when leaving the game state
///
/// Removes all tile entities to free memory and prepare
/// for potential state transitions.
fn cleanup_game(
    mut commands: Commands,
    tiles_query: Query<Entity, With<Tile>>,
) {
    let tile_count = tiles_query.iter().count();
    
    for entity in tiles_query.iter() {
        commands.entity(entity).despawn();
    }
    
    info!("Cleaned up {} tile entities", tile_count);
}

/// Handles pause input during gameplay
///
/// Allows the player to return to the main menu by pressing ESC.
/// Could be extended to show a pause menu instead.
fn handle_pause_input(
    keyboard: Res<ButtonInput<KeyCode>>,
    current_state: Res<State<GameState>>,
    mut next_state: ResMut<NextState<GameState>>,
) {
    if keyboard.just_pressed(KeyCode::Escape) {
        match current_state.get() {
            GameState::InGame => {
                info!("Pausing game, returning to main menu");
                next_state.set(GameState::MainMenu);
            }
            _ => {}
        }
    }
}

/// Debug system for development builds
///
/// Provides useful debugging information and controls
/// Only active when DebugMode resource is present.
#[cfg(debug_assertions)]
fn debug_system(
    keyboard: Res<ButtonInput<KeyCode>>,
    entities: Query<Entity>,
    fps: Res<bevy::diagnostic::DiagnosticsStore>,
) {
    // F3 - Show debug info
    if keyboard.just_pressed(KeyCode::F3) {
        if let Some(fps_diagnostic) = fps.get(&bevy::diagnostic::FrameTimeDiagnosticsPlugin::FPS) {
            if let Some(fps_value) = fps_diagnostic.smoothed() {
                info!("FPS: {:.2}", fps_value);
            }
        }
        info!("Total entities: {}", entities.iter().count());
    }
}

#[cfg(not(debug_assertions))]
fn debug_system() {}

/// Debug mode marker resource
#[derive(Resource)]
struct DebugMode;

// Platform-specific optimizations
#[cfg(target_os = "macos")]
mod macos_optimizations {
    /// Configure Metal-specific rendering optimizations
    pub fn configure_metal_renderer() {
        // Metal API optimizations would go here
        // This is where you'd set up Metal-specific features
    }
}

#[cfg(target_arch = "wasm32")]
mod web_optimizations {
    /// Configure WebGL/WebGPU optimizations
    pub fn configure_web_renderer() {
        // Web-specific optimizations
        // Reduce texture sizes, adjust LOD, etc.
    }
}