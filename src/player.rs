use bevy::prelude::*;
use avian2d::prelude::*;
use crate::game_state::GameState;
use crate::spaceship::CurrentRoom;

pub struct PlayerPlugin;

impl Plugin for PlayerPlugin {
    fn build(&self, app: &mut App) {
        app.add_plugins(PhysicsPlugins::default())
            .insert_resource(Gravity(Vec2::ZERO)) // No gravity in space
            .add_systems(OnEnter(GameState::InGame), spawn_player)
            .add_systems(OnExit(GameState::InGame), despawn_player)
            .add_systems(Update, (
                handle_player_movement,
                update_player_animation,
                camera_follow_player,
            ).run_if(in_state(GameState::InGame)));
    }
}

#[derive(Component)]
pub struct Player {
    pub speed: f32,
    pub in_terminal_mode: bool,
}

#[derive(Component)]
pub struct PlayerCamera;

#[derive(Component)]
struct AnimationTimer(Timer);

const PLAYER_SPEED: f32 = 200.0;
const PLAYER_SIZE: f32 = 24.0;

fn spawn_player(mut commands: Commands) {
    // Spawn the player character
    commands.spawn((
        Player {
            speed: PLAYER_SPEED,
            in_terminal_mode: false,
        },
        Sprite {
            color: Color::srgb(0.7, 0.9, 0.7), // Light green for human
            custom_size: Some(Vec2::splat(PLAYER_SIZE)),
            ..default()
        },
        Transform::from_translation(Vec3::new(0.0, -200.0, 10.0)), // Start in Quarters
        // Avian2D physics components
        RigidBody::Dynamic,
        Collider::circle(PLAYER_SIZE / 2.0),
        LinearVelocity::default(),
        AngularVelocity::default(),
        ExternalForce::default(),
        LockedAxes::ROTATION_LOCKED, // Prevent rotation
        LinearDamping(10.0), // Quick stop when not moving
        AnimationTimer(Timer::from_seconds(0.1, TimerMode::Repeating)),
    ));
    
    // Update camera to follow player
    commands.spawn((
        Camera2d::default(),
        PlayerCamera,
        Camera {
            clear_color: ClearColorConfig::Custom(Color::srgb(0.05, 0.05, 0.1)),
            ..default()
        },
        Transform::from_translation(Vec3::new(0.0, -200.0, 999.0)),
    ));
}

fn handle_player_movement(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut player_query: Query<(&Player, &mut LinearVelocity), Without<PlayerCamera>>,
    time: Res<Time>,
) {
    if let Ok((player, mut velocity)) = player_query.get_single_mut() {
        // Don't move if in terminal mode
        if player.in_terminal_mode {
            velocity.0 = Vec2::ZERO;
            return;
        }
        
        let mut direction = Vec2::ZERO;
        
        // WASD movement
        if keyboard.pressed(KeyCode::KeyW) || keyboard.pressed(KeyCode::ArrowUp) {
            direction.y += 1.0;
        }
        if keyboard.pressed(KeyCode::KeyS) || keyboard.pressed(KeyCode::ArrowDown) {
            direction.y -= 1.0;
        }
        if keyboard.pressed(KeyCode::KeyA) || keyboard.pressed(KeyCode::ArrowLeft) {
            direction.x -= 1.0;
        }
        if keyboard.pressed(KeyCode::KeyD) || keyboard.pressed(KeyCode::ArrowRight) {
            direction.x += 1.0;
        }
        
        // Normalize diagonal movement
        if direction.length() > 0.0 {
            direction = direction.normalize();
        }
        
        // Apply velocity
        velocity.0 = direction * player.speed;
    }
}

fn update_player_animation(
    time: Res<Time>,
    mut player_query: Query<(&LinearVelocity, &mut Sprite, &mut AnimationTimer), With<Player>>,
) {
    if let Ok((velocity, mut sprite, mut timer)) = player_query.get_single_mut() {
        timer.0.tick(time.delta());
        
        // Simple animation: change brightness based on movement
        if velocity.0.length() > 10.0 {
            if timer.0.just_finished() {
                // Animate by slightly changing color
                let base_color = Color::srgb(0.7, 0.9, 0.7);
                let anim_offset = (time.elapsed_secs() * 5.0).sin() * 0.1;
                sprite.color = Color::srgb(
                    base_color.to_srgba().red + anim_offset,
                    base_color.to_srgba().green,
                    base_color.to_srgba().blue + anim_offset,
                );
            }
        } else {
            // Reset to base color when not moving
            sprite.color = Color::srgb(0.7, 0.9, 0.7);
        }
    }
}

fn camera_follow_player(
    player_query: Query<&Transform, (With<Player>, Without<PlayerCamera>)>,
    mut camera_query: Query<&mut Transform, With<PlayerCamera>>,
    current_room: Res<CurrentRoom>,
) {
    if let Ok(player_transform) = player_query.get_single() {
        if let Ok(mut camera_transform) = camera_query.get_single_mut() {
            // Smooth camera follow with room-based constraints
            let target_pos = player_transform.translation;
            
            // Lerp camera position for smooth following
            let lerp_factor = 0.1;
            camera_transform.translation.x = camera_transform.translation.x.lerp(target_pos.x, lerp_factor);
            camera_transform.translation.y = camera_transform.translation.y.lerp(target_pos.y, lerp_factor);
            
            // Keep Z position fixed for camera
            camera_transform.translation.z = 999.0;
        }
    }
}

fn despawn_player(
    mut commands: Commands,
    player_query: Query<Entity, With<Player>>,
    camera_query: Query<Entity, With<PlayerCamera>>,
) {
    for entity in player_query.iter() {
        commands.entity(entity).despawn_recursive();
    }
    for entity in camera_query.iter() {
        commands.entity(entity).despawn_recursive();
    }
}