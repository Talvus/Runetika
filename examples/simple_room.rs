use bevy::prelude::*;
use avian2d::prelude::*;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window {
                title: "Runetika - Blue Dot Test".into(),
                resolution: (1024., 768.).into(),
                ..default()
            }),
            ..default()
        }))
        .add_plugins(PhysicsPlugins::default())
        .add_systems(Startup, setup)
        .add_systems(Update, (movement, debug))
        .run();
}

fn setup(mut commands: Commands) {
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
}

fn movement(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut query: Query<&mut LinearVelocity>,
) {
    if let Ok(mut vel) = query.get_single_mut() {
        let mut dir = Vec2::ZERO;
        if keyboard.pressed(KeyCode::KeyW) { dir.y += 1.0; }
        if keyboard.pressed(KeyCode::KeyS) { dir.y -= 1.0; }
        if keyboard.pressed(KeyCode::KeyA) { dir.x -= 1.0; }
        if keyboard.pressed(KeyCode::KeyD) { dir.x += 1.0; }
        
        vel.0 = if dir.length() > 0.0 {
            dir.normalize() * 250.0
        } else {
            vel.0 * 0.9
        };
    }
}

fn debug(keyboard: Res<ButtonInput<KeyCode>>, mut query: Query<&mut Transform>) {
    if let Ok(mut t) = query.get_single_mut() {
        if keyboard.just_pressed(KeyCode::KeyR) {
            t.translation = Vec3::ZERO;
            println!("Reset!");
        }
        if keyboard.just_pressed(KeyCode::Space) {
            println!("Pos: ({:.1}, {:.1})", t.translation.x, t.translation.y);
        }
    }
}