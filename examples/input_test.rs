use bevy::prelude::*;

#[derive(Component)]
struct Player;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window {
                title: "Input Test - Click window and press keys".into(),
                resolution: (800., 600.).into(),
                focused: true,
                ..default()
            }),
            ..default()
        }))
        .add_systems(Startup, setup)
        .add_systems(Update, (
            test_all_inputs,
            move_with_mouse,
            show_instructions,
        ))
        .run();
}

fn setup(mut commands: Commands) {
    commands.spawn(Camera2d::default());
    
    // Player sprite
    commands.spawn((
        Player,
        Sprite {
            color: Color::srgb(0.3, 0.6, 1.0),
            custom_size: Some(Vec2::splat(50.0)),
            ..default()
        },
        Transform::from_xyz(0.0, 0.0, 0.0),
    ));
    
    // Instructions text
    commands.spawn((
        Text::new("Click anywhere to move the blue square\nPress any key to see it detected in console"),
        TextFont {
            font_size: 20.0,
            ..default()
        },
        Node {
            position_type: PositionType::Absolute,
            top: Val::Px(10.0),
            left: Val::Px(10.0),
            ..default()
        },
    ));
}

fn test_all_inputs(
    keyboard: Res<ButtonInput<KeyCode>>,
    mouse: Res<ButtonInput<MouseButton>>,
    keys: Res<ButtonInput<KeyCode>>,
    mut frame_count: Local<u32>,
) {
    *frame_count += 1;
    
    // Print every 60 frames to avoid spam
    if *frame_count % 60 == 0 {
        println!("Frame {}: Checking inputs...", *frame_count);
    }
    
    // Check for ANY keyboard input
    for key in keys.get_pressed() {
        println!("KEY PRESSED: {:?}", key);
    }
    
    // Check specific keys
    if keyboard.just_pressed(KeyCode::KeyW) { println!("W pressed!"); }
    if keyboard.just_pressed(KeyCode::KeyA) { println!("A pressed!"); }
    if keyboard.just_pressed(KeyCode::KeyS) { println!("S pressed!"); }
    if keyboard.just_pressed(KeyCode::KeyD) { println!("D pressed!"); }
    if keyboard.just_pressed(KeyCode::Space) { println!("Space pressed!"); }
    if keyboard.just_pressed(KeyCode::Escape) { println!("Escape pressed!"); }
    
    // Check mouse
    if mouse.just_pressed(MouseButton::Left) {
        println!("Left mouse clicked!");
    }
}

fn move_with_mouse(
    windows: Query<&Window>,
    mouse: Res<ButtonInput<MouseButton>>,
    mut player: Query<&mut Transform, With<Player>>,
) {
    if let Ok(window) = windows.get_single() {
        if mouse.pressed(MouseButton::Left) {
            if let Some(cursor_pos) = window.cursor_position() {
            // Convert screen coordinates to world coordinates
            let world_pos = Vec3::new(
                cursor_pos.x - window.width() / 2.0,
                -(cursor_pos.y - window.height() / 2.0), // Flip Y
                0.0,
            );
            
            for mut transform in &mut player {
                transform.translation = transform.translation.lerp(world_pos, 0.1);
            }
            
            println!("Moving to mouse position: {:?}", world_pos);
            }
        }
    }
}

fn show_instructions(
    mut frame_count: Local<u32>,
) {
    *frame_count += 1;
    if *frame_count == 1 {
        println!("\n=================================");
        println!("INPUT TEST - TROUBLESHOOTING");
        println!("=================================");
        println!("1. Click anywhere in the window to move the blue square");
        println!("2. Try pressing WASD, Space, or any key");
        println!("3. Check this console for detected inputs");
        println!("4. If mouse works but keyboard doesn't, it's a focus issue");
        println!("=================================\n");
    }
}