use bevy::prelude::*;
use avian2d::prelude::*;
use crate::game_state::GameState;

pub struct MainRoomPlugin;

impl Plugin for MainRoomPlugin {
    fn build(&self, app: &mut App) {
        app.add_plugins(PhysicsPlugins::default())
            .add_systems(OnEnter(GameState::InGame), setup_room)
            .add_systems(Update, (
                player_movement,
                camera_follow,
                debug_controls,
            ).run_if(in_state(GameState::InGame)))
            .add_systems(OnExit(GameState::InGame), cleanup_room);
    }
}

#[derive(Component)]
struct MainRoomEntity;

#[derive(Component)]
pub struct Player { pub speed: f32 }

const ROOM_SIZE: Vec2 = Vec2::new(800.0, 600.0);
const WALL_THICKNESS: f32 = 20.0;
const PLAYER_RADIUS: f32 = 12.0;
const PLAYER_SPEED: f32 = 250.0;

fn setup_room(mut commands: Commands) {
    // Camera
    commands.spawn((
        Camera2d::default(),
        MainRoomEntity,
        Camera {
            clear_color: ClearColorConfig::Custom(Color::srgb(0.03, 0.03, 0.08)),
            ..default()
        },
    ));
    
    // Floor
    commands.spawn((
        MainRoomEntity,
        Sprite {
            color: Color::srgb(0.08, 0.08, 0.15),
            custom_size: Some(ROOM_SIZE),
            ..default()
        },
        Transform::from_xyz(0.0, 0.0, -10.0),
    ));
    
    // Walls - modified to have an opening on the right side for the hallway
    let walls = [
        (0.0, ROOM_SIZE.y/2.0 + WALL_THICKNESS/2.0, ROOM_SIZE.x + WALL_THICKNESS*2.0, WALL_THICKNESS),
        (0.0, -ROOM_SIZE.y/2.0 - WALL_THICKNESS/2.0, ROOM_SIZE.x + WALL_THICKNESS*2.0, WALL_THICKNESS),
        (-ROOM_SIZE.x/2.0 - WALL_THICKNESS/2.0, 0.0, WALL_THICKNESS, ROOM_SIZE.y),
        // Right wall split to create doorway
        (ROOM_SIZE.x/2.0 + WALL_THICKNESS/2.0, 150.0, WALL_THICKNESS, 300.0),  // Top section
        (ROOM_SIZE.x/2.0 + WALL_THICKNESS/2.0, -150.0, WALL_THICKNESS, 300.0), // Bottom section
    ];
    
    for (x, y, w, h) in walls {
        commands.spawn((
            MainRoomEntity,
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
    
    // Spawn the hallway that connects to the maze
    crate::maze::spawn_hallway(&mut commands);
    
    // Player
    commands.spawn((
        MainRoomEntity,
        Player { speed: PLAYER_SPEED },
        Sprite {
            color: Color::srgb(0.3, 0.6, 1.0),
            custom_size: Some(Vec2::splat(PLAYER_RADIUS * 2.0)),
            ..default()
        },
        Transform::from_xyz(0.0, 0.0, 1.0),
        RigidBody::Dynamic,
        Collider::circle(PLAYER_RADIUS),
        LinearVelocity::default(),
        LockedAxes::ROTATION_LOCKED,
        LinearDamping(8.0),
        GravityScale(0.0),
    ));
}

fn player_movement(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut query: Query<(&Player, &mut LinearVelocity)>,
) {
    if let Ok((player, mut velocity)) = query.get_single_mut() {
        let mut dir = Vec2::ZERO;
        
        if keyboard.pressed(KeyCode::KeyW) || keyboard.pressed(KeyCode::ArrowUp) { dir.y += 1.0; }
        if keyboard.pressed(KeyCode::KeyS) || keyboard.pressed(KeyCode::ArrowDown) { dir.y -= 1.0; }
        if keyboard.pressed(KeyCode::KeyA) || keyboard.pressed(KeyCode::ArrowLeft) { dir.x -= 1.0; }
        if keyboard.pressed(KeyCode::KeyD) || keyboard.pressed(KeyCode::ArrowRight) { dir.x += 1.0; }
        
        velocity.0 = if dir.length() > 0.0 {
            dir.normalize() * player.speed
        } else {
            velocity.0 * 0.9
        };
    }
}

fn camera_follow(
    player: Query<&Transform, (With<Player>, Without<Camera2d>)>,
    mut camera: Query<&mut Transform, With<Camera2d>>,
) {
    if let (Ok(p), Ok(mut c)) = (player.get_single(), camera.get_single_mut()) {
        let target = Vec3::new(p.translation.x * 0.3, p.translation.y * 0.3, c.translation.z);
        c.translation = c.translation.lerp(target, 0.08);
    }
}

fn debug_controls(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut player: Query<&mut Transform, With<Player>>,
) {
    if let Ok(mut t) = player.get_single_mut() {
        if keyboard.just_pressed(KeyCode::KeyR) {
            t.translation = Vec3::new(0.0, 0.0, 1.0);
            info!("Position reset");
        }
        if keyboard.just_pressed(KeyCode::Space) {
            info!("Position: ({:.1}, {:.1})", t.translation.x, t.translation.y);
        }
    }
}

fn cleanup_room(mut commands: Commands, query: Query<Entity, With<MainRoomEntity>>) {
    for entity in &query {
        commands.entity(entity).despawn();
    }
}