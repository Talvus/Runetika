use bevy::prelude::*;
use avian2d::prelude::*;

#[derive(Component)]
struct Player;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window {
                title: "Runetika - Working Room".into(),
                resolution: (1024., 768.).into(),
                ..default()
            }),
            ..default()
        }))
        .add_plugins(PhysicsPlugins::default())
        .add_systems(Startup, setup)
        .add_systems(Update, (movement, debug_keys))
        .run();
}

fn setup(mut commands: Commands) {
    println!("Setting up room...");
    
    // Camera
    commands.spawn(Camera2d::default());
    
    // Floor
    commands.spawn((
        Sprite {
            color: Color::srgb(0.1, 0.1, 0.2),
            custom_size: Some(Vec2::new(800.0, 600.0)),
            ..default()
        },
        Transform::from_xyz(0.0, 0.0, -10.0),
    ));
    
    // Walls
    for (x, y, w, h) in [
        (0.0, 310.0, 820.0, 20.0),
        (0.0, -310.0, 820.0, 20.0),
        (-410.0, 0.0, 20.0, 600.0),
        (410.0, 0.0, 20.0, 600.0),
    ] {
        commands.spawn((
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
    
    // Player (blue dot)
    commands.spawn((
        Player,
        Sprite {
            color: Color::srgb(0.3, 0.6, 1.0),
            custom_size: Some(Vec2::splat(24.0)),
            ..default()
        },
        Transform::from_xyz(0.0, 0.0, 1.0),
        RigidBody::Dynamic,
        Collider::circle(12.0),
        LinearVelocity::default(),
        LockedAxes::ROTATION_LOCKED,
        LinearDamping(8.0),
        GravityScale(0.0),
    ));
    
    println!("Room ready! Use Arrow Keys or WASD to move");
}

fn movement(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut query: Query<&mut LinearVelocity, With<Player>>,
) {
    for mut velocity in &mut query {
        let mut direction = Vec2::ZERO;
        
        // Arrow keys
        if keyboard.pressed(KeyCode::ArrowUp) {
            direction.y += 1.0;
        }
        if keyboard.pressed(KeyCode::ArrowDown) {
            direction.y -= 1.0;
        }
        if keyboard.pressed(KeyCode::ArrowLeft) {
            direction.x -= 1.0;
        }
        if keyboard.pressed(KeyCode::ArrowRight) {
            direction.x += 1.0;
        }
        
        // WASD keys  
        if keyboard.pressed(KeyCode::KeyW) {
            direction.y += 1.0;
        }
        if keyboard.pressed(KeyCode::KeyS) {
            direction.y -= 1.0;
        }
        if keyboard.pressed(KeyCode::KeyA) {
            direction.x -= 1.0;
        }
        if keyboard.pressed(KeyCode::KeyD) {
            direction.x += 1.0;
        }
        
        // Apply movement
        if direction.length() > 0.0 {
            velocity.0 = direction.normalize() * 250.0;
        } else {
            velocity.0 *= 0.9;
        }
    }
}

fn debug_keys(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut query: Query<&mut Transform, With<Player>>,
) {
    for mut transform in &mut query {
        if keyboard.just_pressed(KeyCode::KeyR) {
            transform.translation = Vec3::ZERO;
            println!("Position reset!");
        }
        if keyboard.just_pressed(KeyCode::Space) {
            println!("Position: ({:.1}, {:.1})", 
                transform.translation.x, 
                transform.translation.y
            );
        }
    }
}