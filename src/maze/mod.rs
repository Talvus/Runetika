//! Maze generation and gameplay module
//!
//! This module provides maze generation using bevy_knossos with configurable
//! algorithms and difficulty progression. Features include:
//!
//! - Multiple maze generation algorithms (10 options)
//! - Difficulty progression based on completions
//! - Animated portal effects for entrance/exit
//! - Completion counter UI
//! - Bounded camera following in maze area
//!
//! # Usage
//!
//! Add the `MazePlugin` to your Bevy app:
//!
//! ```rust
//! app.add_plugins(MazePlugin);
//! ```

pub mod knossos;
pub mod knossos_renderer;
pub mod portals;
pub mod ui;
pub mod camera;

use bevy::prelude::*;
use avian2d::prelude::*;
use rand::prelude::*;

pub use knossos::KnossosMazeConfig;
pub use knossos_renderer::IsometricRenderConfig;
pub use camera::MazeCameraBounds;

/// Plugin for maze generation and gameplay
pub struct MazePlugin;

impl Plugin for MazePlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(MazeState::default())
            .insert_resource(KnossosMazeConfig::default())
            .insert_resource(MazeCameraBounds::default())
            .insert_resource(IsometricRenderConfig::default())
            .add_event::<MazeCompletedEvent>()
            .add_systems(Update, (
                check_maze_entry,
                check_maze_completion,
                handle_maze_completed,
                portals::animate_portals,
                portals::animate_portal_particles,
                ui::update_maze_ui,
                ui::update_completion_notifications,
                camera::maze_camera_follow,
                camera::reset_camera_bounds,
                camera::maze_camera_zoom,
            ));
    }
}

/// Component marking maze wall entities
#[derive(Component)]
pub struct MazeWall;

/// Component marking maze floor entities
#[derive(Component)]
pub struct MazeFloor;

/// Component marking the maze goal
#[derive(Component)]
pub struct MazeGoal;

/// Component marking any maze entity (for cleanup)
#[derive(Component)]
pub struct MazeEntity;

/// Component marking hallway entities
#[derive(Component)]
pub struct Hallway;

/// Resource tracking maze gameplay state
#[derive(Resource, Default)]
pub struct MazeState {
    /// Whether player is currently in the maze area
    pub in_maze: bool,
    /// Current maze's random seed
    pub maze_seed: u64,
    /// Total number of mazes completed
    pub completions: u32,
    /// True while a `MazeCompletedEvent` is in flight but not yet handled.
    /// Prevents the completion event from firing every frame while the
    /// player is still within the goal radius.
    pub completion_pending: bool,
}

/// Event fired when player completes a maze
#[derive(Event)]
pub struct MazeCompletedEvent;

const CELL_SIZE: f32 = 40.0;

/// Spawn the hallway connecting main room to maze
pub fn spawn_hallway(commands: &mut Commands) -> Vec2 {
    let _hallway_start = Vec2::new(400.0, 0.0);
    let hallway_end = Vec2::new(800.0, 0.0);
    let wall_thickness = 5.0;

    // Hallway floor
    commands.spawn((
        Hallway,
        Sprite {
            color: Color::srgb(0.12, 0.10, 0.18),
            custom_size: Some(Vec2::new(400.0, 80.0)),
            ..default()
        },
        Transform::from_xyz(600.0, 0.0, -9.0),
    ));

    // Hallway walls
    for (x, y, w, h) in [
        (600.0, 50.0, 400.0, wall_thickness),  // Top wall
        (600.0, -50.0, 400.0, wall_thickness), // Bottom wall
    ] {
        commands.spawn((
            Hallway,
            Sprite {
                color: Color::srgb(0.05, 0.05, 0.12),
                custom_size: Some(Vec2::new(w, h)),
                ..default()
            },
            Transform::from_xyz(x, y, -5.0),
            RigidBody::Static,
            Collider::rectangle(w, h),
        ));
    }

    // Entrance indicator (green)
    portals::spawn_entrance_portal(commands, Vec2::new(410.0, 0.0), 50.0);

    // Direction sign
    commands.spawn((
        Hallway,
        Text::new("→ MAZE"),
        TextFont {
            font_size: 16.0,
            ..default()
        },
        Node {
            position_type: PositionType::Absolute,
            left: Val::Px(550.0),
            top: Val::Px(380.0),
            ..default()
        },
    ));

    hallway_end
}

/// Generate a new maze with current configuration
///
/// When `render_config.enabled` is true, uses isometric 2.5D rendering
/// for the Silicon Mind aesthetic. Otherwise, uses flat 2D rendering.
pub fn generate_maze(
    commands: &mut Commands,
    config: &KnossosMazeConfig,
    offset: Vec2,
) {
    generate_maze_with_rendering(commands, config, offset, &IsometricRenderConfig::default())
}

/// Generate maze with explicit rendering configuration
pub fn generate_maze_with_rendering(
    commands: &mut Commands,
    config: &KnossosMazeConfig,
    offset: Vec2,
    render_config: &IsometricRenderConfig,
) {
    match knossos::generate_knossos_maze(config) {
        Ok(maze) => {
            if render_config.enabled {
                // Use isometric WFC-style rendering
                knossos_renderer::spawn_isometric_knossos_maze(
                    commands, &maze, config, render_config, offset
                );
                info!(
                    "Generated {}x{} isometric maze using {} (difficulty {}, theme {:?})",
                    config.width,
                    config.height,
                    config.algorithm.name(),
                    config.algorithm.difficulty(),
                    render_config.theme
                );
            } else {
                // Use standard flat rendering
                knossos::spawn_knossos_maze_entities(commands, &maze, config, offset);
                info!(
                    "Generated {}x{} flat maze using {} (difficulty {})",
                    config.width,
                    config.height,
                    config.algorithm.name(),
                    config.algorithm.difficulty()
                );
            }
        }
        Err(e) => {
            error!("Failed to generate maze: {}", e);
            // Fallback: generate simple maze
            generate_fallback_maze(commands, config, offset);
        }
    }
}

/// Fallback maze generation if knossos fails
fn generate_fallback_maze(commands: &mut Commands, config: &KnossosMazeConfig, offset: Vec2) {
    warn!("Using fallback maze generation");

    // Simple grid with walls on edges
    for y in 0..config.height {
        for x in 0..config.width {
            let pos = Vec2::new(
                x as f32 * config.cell_size + offset.x,
                -(y as f32 * config.cell_size) + offset.y,
            );

            // Floor
            commands.spawn((
                MazeEntity,
                MazeFloor,
                Sprite {
                    color: Color::srgb(0.15, 0.12, 0.25),
                    custom_size: Some(Vec2::splat(config.cell_size - 2.0)),
                    ..default()
                },
                Transform::from_xyz(pos.x, pos.y, -10.0),
            ));

            // Boundary walls
            if x == 0 || y == 0 || x == config.width - 1 || y == config.height - 1 {
                commands.spawn((
                    MazeEntity,
                    MazeWall,
                    Sprite {
                        color: Color::srgb(0.02, 0.02, 0.06),
                        custom_size: Some(Vec2::splat(config.cell_size)),
                        ..default()
                    },
                    Transform::from_xyz(pos.x, pos.y, -5.0),
                    RigidBody::Static,
                    Collider::rectangle(config.cell_size, config.cell_size),
                ));
            }
        }
    }

    // Goal
    let goal_pos = Vec2::new(
        (config.width - 2) as f32 * config.cell_size + offset.x,
        -((config.height - 2) as f32 * config.cell_size) + offset.y,
    );
    portals::spawn_exit_portal(commands, goal_pos, config.cell_size * 0.8);
}

/// Clear all maze entities
pub fn clear_maze(commands: &mut Commands, maze_query: Query<Entity, With<MazeEntity>>) {
    for entity in maze_query.iter() {
        commands.entity(entity).despawn();
    }
}

/// System to check if player has entered the maze area
fn check_maze_entry(
    player_query: Query<&Transform, With<crate::main_room::Player>>,
    mut maze_state: ResMut<MazeState>,
    mut config: ResMut<KnossosMazeConfig>,
    mut bounds: ResMut<MazeCameraBounds>,
    render_config: Res<IsometricRenderConfig>,
    mut commands: Commands,
    maze_query: Query<Entity, With<MazeEntity>>,
    ui_query: Query<Entity, With<ui::MazeCompletionUI>>,
) {
    let Ok(player_transform) = player_query.single() else {
        return;
    };

    let player_x = player_transform.translation.x;
    let player_y = player_transform.translation.y;

    let in_hallway = player_x > 400.0 && player_x < 800.0 && player_y.abs() < 40.0;
    let in_maze_area = player_x > 800.0;

    if in_maze_area && !maze_state.in_maze {
        // Enter maze
        maze_state.in_maze = true;
        maze_state.maze_seed = rand::thread_rng().gen();

        // Update config for difficulty
        knossos::update_config_for_difficulty(&mut config, maze_state.completions);
        config.seed = Some(maze_state.maze_seed);

        // Clear old maze if exists
        clear_maze(&mut commands, maze_query);

        // Generate new maze with isometric rendering
        let maze_offset = Vec2::new(850.0, 200.0);
        generate_maze_with_rendering(&mut commands, &config, maze_offset, &render_config);

        // Set camera bounds
        *bounds = MazeCameraBounds::from_config(&config, maze_offset);

        // Spawn UI
        ui::spawn_maze_ui(&mut commands);

        info!(
            "Entered maze #{} (seed: {}, algorithm: {}, isometric: {})",
            maze_state.completions + 1,
            maze_state.maze_seed,
            config.algorithm.name(),
            render_config.enabled
        );
    } else if !in_hallway && !in_maze_area && maze_state.in_maze {
        // Left maze area
        maze_state.in_maze = false;
        bounds.active = false;

        // Clean up
        clear_maze(&mut commands, maze_query);
        ui::despawn_maze_ui(&mut commands, ui_query);

        info!("Returned to main room");
    }
}

/// System to check if player has reached the goal
fn check_maze_completion(
    player_query: Query<&Transform, With<crate::main_room::Player>>,
    goal_query: Query<&Transform, With<MazeGoal>>,
    mut maze_state: ResMut<MazeState>,
    mut events: EventWriter<MazeCompletedEvent>,
) {
    if !maze_state.in_maze || maze_state.completion_pending {
        return;
    }

    let Ok(player_transform) = player_query.single() else {
        return;
    };

    let Ok(goal_transform) = goal_query.single() else {
        return;
    };

    let distance = player_transform
        .translation
        .truncate()
        .distance(goal_transform.translation.truncate());

    if distance < CELL_SIZE * 0.5 {
        maze_state.completion_pending = true;
        events.write(MazeCompletedEvent);
    }
}

/// System to handle maze completion
fn handle_maze_completed(
    mut events: EventReader<MazeCompletedEvent>,
    mut maze_state: ResMut<MazeState>,
    mut config: ResMut<KnossosMazeConfig>,
    mut player_query: Query<&mut Transform, With<crate::main_room::Player>>,
    mut commands: Commands,
    maze_query: Query<Entity, With<MazeEntity>>,
    mut bounds: ResMut<MazeCameraBounds>,
) {
    for _ in events.read() {
        maze_state.completions += 1;
        maze_state.completion_pending = false;
        info!("🎉 Maze completed! Total: {}", maze_state.completions);

        // Show notification
        ui::show_completion_notification(&mut commands, maze_state.completions);

        // Teleport player back to hallway
        if let Ok(mut player_transform) = player_query.single_mut() {
            player_transform.translation = Vec3::new(450.0, 0.0, 1.0);
        }

        // Clear current maze
        clear_maze(&mut commands, maze_query);

        // Update config for new difficulty
        knossos::update_config_for_difficulty(&mut config, maze_state.completions);
        maze_state.maze_seed = rand::thread_rng().gen();
        config.seed = Some(maze_state.maze_seed);

        // Generate new maze
        let maze_offset = Vec2::new(850.0, 200.0);
        generate_maze(&mut commands, &config, maze_offset);

        // Update camera bounds
        *bounds = MazeCameraBounds::from_config(&config, maze_offset);

        info!(
            "New maze generated! (seed: {}, algorithm: {})",
            maze_state.maze_seed,
            config.algorithm.name()
        );
    }
}
