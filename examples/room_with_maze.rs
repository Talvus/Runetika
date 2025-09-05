use bevy::prelude::*;
use avian2d::prelude::*;

// Import our maze module
mod maze;
use maze::{MazePlugin, spawn_hallway};

#[derive(Component)]
pub struct Player;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window {
                title: "Runetika - Room with Procedural Maze".into(),
                resolution: (1280., 800.).into(),
                ..default()
            }),
            ..default()
        }))
        .add_plugins(PhysicsPlugins::default())
        .add_plugins(MazePlugin)  // Add our maze plugin
        .add_systems(Startup, setup)
        .add_systems(Update, (
            movement,
            camera_follow,
            debug_keys,
            display_stats,
        ))
        .run();
}

fn setup(mut commands: Commands) {
    println!("=================================");
    println!("MAZE RUNNER - Tutorial");
    println!("=================================");
    println!("1. Start in the blue room");
    println!("2. Go RIGHT through the green door");
    println!("3. Enter the MAZE area");
    println!("4. Find the GREEN GOAL square");
    println!("5. You'll respawn with a NEW maze!");
    println!("=================================\n");
    
    // Camera with wider view
    commands.spawn((
        Camera2d::default(),
        Transform::from_xyz(0.0, 0.0, 100.0),
    ));
    
    // Main Room Floor
    commands.spawn((
        Sprite {
            color: Color::srgb(0.1, 0.1, 0.2),
            custom_size: Some(Vec2::new(800.0, 600.0)),
            ..default()
        },
        Transform::from_xyz(0.0, 0.0, -10.0),
    ));
    
    // Room label
    commands.spawn((
        Text::new("MAIN ROOM"),
        TextFont {
            font_size: 20.0,
            ..default()
        },
        Node {
            position_type: PositionType::Absolute,
            left: Val::Px(100.0),
            top: Val::Px(100.0),
            ..default()
        },
    ));
    
    // Main Room Walls (with opening for hallway)
    let walls = [
        // Top wall
        (0.0, 310.0, 820.0, 20.0),
        // Bottom wall  
        (0.0, -310.0, 820.0, 20.0),
        // Left wall
        (-410.0, 0.0, 20.0, 600.0),
        // Right wall (top part)
        (410.0, 150.0, 20.0, 300.0),
        // Right wall (bottom part)
        (410.0, -150.0, 20.0, 300.0),
    ];
    
    for (x, y, w, h) in walls {
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
    
    // Spawn the hallway connecting room to maze
    spawn_hallway(&mut commands);
    
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
}

fn movement(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut query: Query<&mut LinearVelocity, With<Player>>,
) {
    for mut velocity in &mut query {
        let mut direction = Vec2::ZERO;
        
        // Arrow keys
        if keyboard.pressed(KeyCode::ArrowUp) { direction.y += 1.0; }
        if keyboard.pressed(KeyCode::ArrowDown) { direction.y -= 1.0; }
        if keyboard.pressed(KeyCode::ArrowLeft) { direction.x -= 1.0; }
        if keyboard.pressed(KeyCode::ArrowRight) { direction.x += 1.0; }
        
        // WASD keys  
        if keyboard.pressed(KeyCode::KeyW) { direction.y += 1.0; }
        if keyboard.pressed(KeyCode::KeyS) { direction.y -= 1.0; }
        if keyboard.pressed(KeyCode::KeyA) { direction.x -= 1.0; }
        if keyboard.pressed(KeyCode::KeyD) { direction.x += 1.0; }
        
        // Apply movement with speed boost in maze area
        if direction.length() > 0.0 {
            let speed = 250.0;
            velocity.0 = direction.normalize() * speed;
        } else {
            velocity.0 *= 0.9;
        }
    }
}

fn camera_follow(
    player_query: Query<&Transform, (With<Player>, Without<Camera2d>)>,
    mut camera_query: Query<&mut Transform, With<Camera2d>>,
) {
    if let (Ok(player), Ok(mut camera)) = (player_query.get_single(), camera_query.get_single_mut()) {
        // Smooth camera follow with offset based on player position
        let target = if player.translation.x > 600.0 {
            // In maze area - offset camera to show more
            Vec3::new(
                player.translation.x * 0.5 + 200.0,
                player.translation.y * 0.5,
                camera.translation.z,
            )
        } else {
            // In main room - gentle follow
            Vec3::new(
                player.translation.x * 0.3,
                player.translation.y * 0.3,
                camera.translation.z,
            )
        };
        
        camera.translation = camera.translation.lerp(target, 0.1);
    }
}

fn debug_keys(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut player_query: Query<&mut Transform, With<Player>>,
) {
    if let Ok(mut transform) = player_query.get_single_mut() {
        if keyboard.just_pressed(KeyCode::KeyR) {
            transform.translation = Vec3::new(0.0, 0.0, 1.0);
            println!("Reset to main room!");
        }
        if keyboard.just_pressed(KeyCode::Space) {
            println!("Position: ({:.1}, {:.1})", 
                transform.translation.x, 
                transform.translation.y
            );
        }
    }
}

fn display_stats(
    maze_state: Res<maze::MazeState>,
    mut last_state: Local<bool>,
) {
    if maze_state.in_maze != *last_state {
        *last_state = maze_state.in_maze;
        if maze_state.in_maze {
            println!("📍 Location: MAZE AREA");
        } else {
            println!("📍 Location: MAIN ROOM");
        }
    }
}

// Re-export maze module components
pub use maze::{MazeWall, MazeFloor, MazeGoal, MazeEntity, Hallway};