/// Core game modules - Each module encapsulates a major game system
/// 
/// # Architecture Overview
/// The game follows a modular architecture where each system is self-contained:
/// - **terminal**: The primary gameplay interface (command-line in space)
/// - **menu**: Navigation and game flow control  
/// - **game_state**: State machine managing game phases
/// - **credits**: Acknowledgments and team information
/// - **settings**: Game configuration and preferences
/// 
/// # Design Philosophy
/// Think of these modules as planets in a solar system - each has its own
/// gravity (internal logic) but they orbit around the central game loop.
mod terminal;
mod menu;
mod game_state;
mod credits;
mod settings;

use bevy::prelude::*;
use terminal::TerminalPlugin;
use menu::MainMenuPlugin;
use game_state::{GameStatePlugin, GameState};
use credits::CreditsPlugin;
use settings::SettingsPlugin;

/// Tile component - Represents a single map cell
/// 
/// # Abstract Concept
/// Tiles are the atomic units of space in our game world.
/// They form a discrete lattice that approximates continuous space.
/// 
/// # Practical Usage
/// Each tile is a visual square on the game map that players can see.
/// Tiles will eventually have properties like walkability, resources, etc.
#[derive(Component)]
struct Tile;

/// MapSize resource - Defines the dimensions of the game world
/// 
/// # Mathematical Model
/// The map is a 2D grid in ℤ² (integer coordinates) with finite bounds.
/// This creates a toroidal topology if we add wraparound.
/// 
/// # Game Context  
/// This sets how big the playable area is. Bigger maps = more exploration
/// but also more memory usage and potentially slower performance.
#[derive(Resource)]
struct MapSize {
    width: u32,
    height: u32,
}

/// Initialize the main game camera
/// 
/// # Visual Philosophy
/// The camera is our window into the game world. The dark purple background
/// (0.02, 0.0, 0.04) creates a deep space atmosphere.
/// 
/// # Technical Details
/// Uses Bevy's 2D camera with orthographic projection.
/// The clear color sets the background when nothing is rendered.
fn setup_camera(mut commands: Commands) {
    commands.spawn((
        Camera2d::default(),
        // Set clear color to dark space
        Camera {
            clear_color: ClearColorConfig::Custom(Color::srgb(0.02, 0.0, 0.04)),
            ..default()
        },
    ));
}

/// Generate the initial game map
/// 
/// # Procedural Generation Concept
/// Currently creates a simple 10x10 grid. This is a placeholder for
/// future procedural generation algorithms (Perlin noise, cellular automata, etc.)
/// 
/// # Coordinate System
/// Map tiles are centered around (0,0) in world space.
/// Each tile is 32 pixels apart with 30-pixel visual size (creates grid gaps).
fn setup_map(mut commands: Commands) {
    let map = MapSize { width: 10, height: 10 };
    commands.insert_resource(map);

    for x in 0..10u32 {
        for y in 0..10u32 {
            commands.spawn((
                Tile,
                Sprite {
                    color: Color::srgb(0.1, 0.2, 0.1), 
                    custom_size: Some(Vec2::splat(30.0)), 
                    ..Default::default()
                },
                Transform::from_xyz(
                    (x as f32 - 5.0) * 32.0, 
                    (y as f32 - 5.0) * 32.0, 
                    -1.0
                ),
            ));
        }
    }
}

/// Main entry point - Configures and launches the Bevy application
/// 
/// # Application Architecture
/// The main function sets up the Bevy app with:
/// 1. **DefaultPlugins**: Core Bevy functionality (rendering, input, etc.)
/// 2. **Custom Plugins**: Our game-specific systems
/// 3. **Systems**: Functions that run at specific times
/// 
/// # Execution Flow
/// - Startup: Camera and initial setup
/// - State-based: Different systems run based on current GameState
/// - Update: Continuous gameplay logic
/// 
/// # For Abstract Thinkers
/// This creates an event-driven state machine where systems react to
/// state transitions and input events in a deterministic order.
/// 
/// # For Concrete Thinkers
/// This is where the game starts. It sets up the window, loads our code,
/// and begins the game loop that runs 60+ times per second.
fn main() {
    App::new()
        .add_plugins(DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window { 
                title: "Runetika - Cosmic Odyssey".into(), 
                resolution: (1280., 800.).into(), 
                ..default() 
            }),
            ..default()
        }))
        .add_plugins((
            GameStatePlugin,
            MainMenuPlugin,
            TerminalPlugin,
            CreditsPlugin,
            SettingsPlugin,
        ))
        .add_systems(Startup, setup_camera)
        .add_systems(OnEnter(GameState::InGame), setup_map)
        .add_systems(OnExit(GameState::InGame), cleanup_game)
        .add_systems(Update, handle_pause_input.run_if(in_state(GameState::InGame)))
        .run();
}

/// Clean up game entities when exiting gameplay
/// 
/// # Memory Management
/// Prevents memory leaks by despawning entities that are no longer needed.
/// Bevy's ECS handles the actual memory deallocation.
/// 
/// # Why This Matters
/// Without cleanup, switching between menu and game repeatedly would
/// accumulate entities, eventually slowing down the game.
fn cleanup_game(
    mut commands: Commands,
    tiles_query: Query<Entity, With<Tile>>,
) {
    for entity in tiles_query.iter() {
        commands.entity(entity).despawn();
    }
}

/// Handle pause/menu toggle during gameplay
/// 
/// # Input Design
/// ESC key provides a universal "back out" mechanism.
/// This follows standard game UX conventions.
/// 
/// # State Transition
/// Moves from InGame -> MainMenu state, triggering cleanup and menu setup.
fn handle_pause_input(
    keyboard: Res<ButtonInput<KeyCode>>,
    current_state: Res<State<GameState>>,
    mut next_state: ResMut<NextState<GameState>>,
) {
    if keyboard.just_pressed(KeyCode::Escape) {
        match current_state.get() {
            GameState::InGame => next_state.set(GameState::MainMenu),
            _ => {}
        }
    }
}
