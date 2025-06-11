use bevy::prelude::*;
use avian2d::prelude::*;

#[derive(Component)]
struct Tile;

#[derive(Resource)]
struct MapSize {
    width: u32,
    height: u32,
}

fn setup_map(mut commands: Commands) {
    let map = MapSize { width: 10, height: 10 };
    commands.insert_resource(map);

    for x in 0..10u32 {
        for y in 0..10u32 {
            commands.spawn(
                (
                    Tile,
                    SpriteBundle {
                        transform: Transform::from_xyz(x as f32 * 32., y as f32 * 32., 0.0),
                        sprite: Sprite { color: Color::DARK_GREEN, custom_size: Some(Vec2::splat(30.0)), ..Default::default() },
                        ..Default::default()
                    },
                )
            );
        }
    }
}

fn main() {
    App::new()
        .add_plugins(DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window { title: "Runetika".into(), resolution: (640., 480.).into(), ..default() }),
            ..default()
        }))
        .add_systems(Startup, setup_map)
        .run();
}
