mod terminal;

use bevy::prelude::*;
use terminal::TerminalPlugin;

#[derive(Component)]
struct Tile;

#[derive(Resource)]
struct MapSize {
    width: u32,
    height: u32,
}

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

fn main() {
    App::new()
        .add_plugins(DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window { 
                title: "Runetika".into(), 
                resolution: (1024., 768.).into(), 
                ..default() 
            }),
            ..default()
        }))
        .add_plugins(TerminalPlugin)
        .add_systems(Startup, (setup_camera, setup_map))
        .run();
}
