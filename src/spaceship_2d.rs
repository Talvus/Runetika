use bevy::prelude::*;
use avian2d::prelude::*;
use crate::game_state::GameState;

pub struct Spaceship2DPlugin;

impl Plugin for Spaceship2DPlugin {
    fn build(&self, app: &mut App) {
        app.add_systems(OnEnter(GameState::InGame), (
            setup_isometric_camera,
            setup_spaceship_floor,
            spawn_player_dot,
        ).chain())
            .add_systems(Update, (
                player_movement,
                update_depth_sorting,
                camera_follow_player,
            ).run_if(in_state(GameState::InGame)))
            .add_systems(OnExit(GameState::InGame), cleanup_spaceship);
    }
}

// Components
#[derive(Component)]
pub struct SpaceshipFloor;

#[derive(Component)]
pub struct Player2D {
    speed: f32,
}

#[derive(Component)]
pub struct IsometricCamera;

#[derive(Component)]
pub struct DepthSorted;

// Constants for 2.5D isometric view
const ISOMETRIC_ANGLE: f32 = 30.0; // Degrees
const TILE_WIDTH: f32 = 64.0;
const TILE_HEIGHT: f32 = 32.0;
const PLAYER_SPEED: f32 = 200.0;
const PLAYER_SIZE: f32 = 16.0;

fn setup_isometric_camera(mut commands: Commands) {
    // Remove existing camera if any
    commands.spawn((
        Camera2d::default(),
        IsometricCamera,
        Transform::from_xyz(0.0, 100.0, 1000.0)
            .with_scale(Vec3::new(1.0, 1.0, 1.0)),
        Camera {
            clear_color: ClearColorConfig::Custom(Color::srgb(0.05, 0.05, 0.1)),
            ..default()
        },
    ));
}

fn setup_spaceship_floor(
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<ColorMaterial>>,
) {
    // Create the main spaceship floor area
    let floor_width = 20; // tiles
    let floor_height = 15; // tiles
    
    // Create floor tiles in isometric pattern
    for x in 0..floor_width {
        for y in 0..floor_height {
            let world_pos = isometric_to_world(x as f32, y as f32);
            
            // Alternate tile colors for visual depth
            let color = if (x + y) % 2 == 0 {
                Color::srgb(0.15, 0.15, 0.25)
            } else {
                Color::srgb(0.12, 0.12, 0.22)
            };
            
            // Create diamond-shaped tile for isometric view
            commands.spawn((
                SpaceshipFloor,
                DepthSorted,
                Sprite {
                    color,
                    custom_size: Some(Vec2::new(TILE_WIDTH, TILE_HEIGHT)),
                    ..default()
                },
                Transform::from_translation(Vec3::new(
                    world_pos.x,
                    world_pos.y,
                    -100.0 - y as f32, // Depth sorting
                )),
            ));
        }
    }
    
    // Add walls for depth
    create_walls(&mut commands, floor_width, floor_height);
}

fn create_walls(commands: &mut Commands, width: u32, height: u32) {
    // Back wall
    for x in 0..width {
        let world_pos = isometric_to_world(x as f32, height as f32);
        commands.spawn((
            SpaceshipFloor,
            DepthSorted,
            Sprite {
                color: Color::srgb(0.08, 0.08, 0.15),
                custom_size: Some(Vec2::new(TILE_WIDTH, TILE_HEIGHT * 2.0)),
                ..default()
            },
            Transform::from_translation(Vec3::new(
                world_pos.x,
                world_pos.y + TILE_HEIGHT,
                -100.0 - height as f32 - 1.0,
            )),
        ));
    }
    
    // Right wall
    for y in 0..height {
        let world_pos = isometric_to_world(width as f32, y as f32);
        commands.spawn((
            SpaceshipFloor,
            DepthSorted,
            Sprite {
                color: Color::srgb(0.1, 0.1, 0.18),
                custom_size: Some(Vec2::new(TILE_WIDTH * 0.5, TILE_HEIGHT * 2.0)),
                ..default()
            },
            Transform::from_translation(Vec3::new(
                world_pos.x + TILE_WIDTH * 0.25,
                world_pos.y + TILE_HEIGHT,
                -100.0 - y as f32 - 0.5,
            )),
        ));
    }
}

fn spawn_player_dot(mut commands: Commands) {
    // Spawn blue dot as temporary player character
    let start_pos = isometric_to_world(10.0, 7.0);
    
    commands.spawn((
        Player2D {
            speed: PLAYER_SPEED,
        },
        DepthSorted,
        Sprite {
            color: Color::srgb(0.2, 0.5, 1.0), // Blue dot
            custom_size: Some(Vec2::splat(PLAYER_SIZE)),
            ..default()
        },
        Transform::from_translation(Vec3::new(
            start_pos.x,
            start_pos.y,
            0.0, // Player always on top
        )),
        // Add physics components for smooth movement
        RigidBody::Dynamic,
        Collider::circle(PLAYER_SIZE / 2.0),
        LinearVelocity::default(),
        LockedAxes::ROTATION_LOCKED,
        LinearDamping(10.0),
    ));
}

fn player_movement(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut player_query: Query<(&Player2D, &mut LinearVelocity)>,
    time: Res<Time>,
) {
    if let Ok((player, mut velocity)) = player_query.get_single_mut() {
        let mut movement = Vec2::ZERO;
        
        // WASD movement in isometric space
        if keyboard.pressed(KeyCode::KeyW) || keyboard.pressed(KeyCode::ArrowUp) {
            movement.x -= 1.0;
            movement.y += 0.5;
        }
        if keyboard.pressed(KeyCode::KeyS) || keyboard.pressed(KeyCode::ArrowDown) {
            movement.x += 1.0;
            movement.y -= 0.5;
        }
        if keyboard.pressed(KeyCode::KeyA) || keyboard.pressed(KeyCode::ArrowLeft) {
            movement.x -= 1.0;
            movement.y -= 0.5;
        }
        if keyboard.pressed(KeyCode::KeyD) || keyboard.pressed(KeyCode::ArrowRight) {
            movement.x += 1.0;
            movement.y += 0.5;
        }
        
        // Normalize and apply movement
        if movement.length() > 0.0 {
            movement = movement.normalize();
            velocity.0 = movement * player.speed;
        } else {
            velocity.0 = Vec2::ZERO;
        }
    }
}

fn update_depth_sorting(
    mut query: Query<(&mut Transform, &DepthSorted)>,
) {
    // Sort entities by their Y position for proper 2.5D layering
    for (mut transform, _) in query.iter_mut() {
        // Use Y position to determine Z depth
        transform.translation.z = -transform.translation.y * 0.01;
    }
}

fn camera_follow_player(
    player_query: Query<&Transform, (With<Player2D>, Without<IsometricCamera>)>,
    mut camera_query: Query<&mut Transform, With<IsometricCamera>>,
) {
    if let Ok(player_transform) = player_query.get_single() {
        if let Ok(mut camera_transform) = camera_query.get_single_mut() {
            // Smooth camera follow
            let target = Vec3::new(
                player_transform.translation.x,
                player_transform.translation.y + 50.0, // Offset for better view
                camera_transform.translation.z,
            );
            
            camera_transform.translation = camera_transform.translation.lerp(target, 0.1);
        }
    }
}

fn cleanup_spaceship(
    mut commands: Commands,
    floor_query: Query<Entity, With<SpaceshipFloor>>,
    player_query: Query<Entity, With<Player2D>>,
) {
    // Clean up all spaceship entities
    for entity in floor_query.iter() {
        commands.entity(entity).despawn();
    }
    
    for entity in player_query.iter() {
        commands.entity(entity).despawn();
    }
}

// Helper function to convert isometric grid coordinates to world position
fn isometric_to_world(x: f32, y: f32) -> Vec2 {
    Vec2::new(
        (x - y) * TILE_WIDTH * 0.5,
        (x + y) * TILE_HEIGHT * 0.5,
    )
}

// Helper function to convert world position to isometric grid coordinates
fn world_to_isometric(world_x: f32, world_y: f32) -> Vec2 {
    let x = (world_x / (TILE_WIDTH * 0.5) + world_y / (TILE_HEIGHT * 0.5)) * 0.5;
    let y = (world_y / (TILE_HEIGHT * 0.5) - world_x / (TILE_WIDTH * 0.5)) * 0.5;
    Vec2::new(x, y)
}