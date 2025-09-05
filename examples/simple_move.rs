use bevy::prelude::*;

#[derive(Component)]
struct Player;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_systems(Startup, setup)
        .add_systems(Update, movement)
        .run();
}

fn setup(mut commands: Commands) {
    // Camera
    commands.spawn(Camera2d::default());
    
    // Player - simple blue square
    commands.spawn((
        Player,
        Sprite {
            color: Color::srgb(0.3, 0.6, 1.0),
            custom_size: Some(Vec2::splat(50.0)),
            ..default()
        },
        Transform::from_xyz(0.0, 0.0, 0.0),
    ));
    
    println!("Game started! Use WASD to move the blue square.");
}

fn movement(
    time: Res<Time>,
    keyboard: Res<ButtonInput<KeyCode>>,
    mut query: Query<&mut Transform, With<Player>>,
) {
    let speed = 200.0 * time.delta_secs();
    
    for mut transform in &mut query {
        if keyboard.pressed(KeyCode::KeyW) {
            transform.translation.y += speed;
        }
        if keyboard.pressed(KeyCode::KeyS) {
            transform.translation.y -= speed;
        }
        if keyboard.pressed(KeyCode::KeyA) {
            transform.translation.x -= speed;
        }
        if keyboard.pressed(KeyCode::KeyD) {
            transform.translation.x += speed;
        }
    }
}