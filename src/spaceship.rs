use bevy::prelude::*;
use avian2d::prelude::*;
use crate::game_state::GameState;

pub struct SpaceshipPlugin;

impl Plugin for SpaceshipPlugin {
    fn build(&self, app: &mut App) {
        app.add_systems(OnEnter(GameState::InGame), setup_spaceship_level)
            .add_systems(OnExit(GameState::InGame), cleanup_spaceship_level)
            .add_systems(Update, (
                update_room_visibility,
                check_room_transitions,
            ).run_if(in_state(GameState::InGame)));
    }
}

#[derive(Component)]
pub struct SpaceshipLevel;

#[derive(Component, Clone, Copy, PartialEq, Eq)]
pub enum RoomType {
    Bridge,      // Command center with main terminal
    Engineering, // Power systems and machinery
    Quarters,    // Living space
    Corridor,    // Connecting hallway
    Storage,     // Supply room with puzzle elements
}

#[derive(Component)]
pub struct Room {
    pub room_type: RoomType,
    pub bounds: Rect,
    pub active: bool,
}

#[derive(Component)]
pub struct Wall;

#[derive(Component)]
pub struct Floor;

#[derive(Component)]
pub struct Door {
    pub connects: (RoomType, RoomType),
    pub locked: bool,
}

#[derive(Resource)]
pub struct CurrentRoom {
    pub room_type: RoomType,
}

const TILE_SIZE: f32 = 32.0;
const WALL_COLOR: Color = Color::srgb(0.15, 0.15, 0.2);
const FLOOR_COLOR: Color = Color::srgb(0.25, 0.25, 0.35);
const DOOR_COLOR: Color = Color::srgb(0.4, 0.6, 0.8);

fn setup_spaceship_level(mut commands: Commands) {
    commands.insert_resource(CurrentRoom { room_type: RoomType::Quarters });
    
    // Create the 5-room spaceship layout
    // Layout:
    //     [Bridge]
    //        |
    //   [Engineering]
    //        |
    //   [Corridor]---[Storage]
    //        |
    //   [Quarters]
    
    // Define room positions and sizes
    let rooms = vec![
        (RoomType::Bridge, Vec2::new(0.0, 400.0), Vec2::new(300.0, 200.0)),
        (RoomType::Engineering, Vec2::new(0.0, 200.0), Vec2::new(350.0, 150.0)),
        (RoomType::Corridor, Vec2::new(0.0, 0.0), Vec2::new(400.0, 100.0)),
        (RoomType::Storage, Vec2::new(300.0, 0.0), Vec2::new(200.0, 150.0)),
        (RoomType::Quarters, Vec2::new(0.0, -200.0), Vec2::new(250.0, 150.0)),
    ];
    
    for (room_type, position, size) in rooms {
        create_room(&mut commands, room_type, position, size);
    }
    
    // Create doors between rooms
    create_door(&mut commands, Vec2::new(0.0, 300.0), (RoomType::Bridge, RoomType::Engineering), false);
    create_door(&mut commands, Vec2::new(0.0, 100.0), (RoomType::Engineering, RoomType::Corridor), false);
    create_door(&mut commands, Vec2::new(200.0, 0.0), (RoomType::Corridor, RoomType::Storage), true); // Initially locked
    create_door(&mut commands, Vec2::new(0.0, -100.0), (RoomType::Corridor, RoomType::Quarters), false);
}

fn create_room(commands: &mut Commands, room_type: RoomType, position: Vec2, size: Vec2) {
    let half_size = size * 0.5;
    let bounds = Rect::from_center_half_size(position, half_size);
    
    // Create room entity
    commands.spawn((
        Room {
            room_type,
            bounds,
            active: room_type == RoomType::Quarters, // Start in Quarters
        },
        SpaceshipLevel,
        Transform::from_translation(position.extend(0.0)),
        GlobalTransform::default(),
        Visibility::default(),
        InheritedVisibility::default(),
        ViewVisibility::default(),
    ));
    
    // Create floor tiles
    let tiles_x = (size.x / TILE_SIZE) as i32;
    let tiles_y = (size.y / TILE_SIZE) as i32;
    
    for x in 0..tiles_x {
        for y in 0..tiles_y {
            let tile_pos = position + Vec2::new(
                (x as f32 - tiles_x as f32 / 2.0 + 0.5) * TILE_SIZE,
                (y as f32 - tiles_y as f32 / 2.0 + 0.5) * TILE_SIZE,
            );
            
            commands.spawn((
                Floor,
                SpaceshipLevel,
                Sprite {
                    color: FLOOR_COLOR,
                    custom_size: Some(Vec2::splat(TILE_SIZE - 2.0)),
                    ..default()
                },
                Transform::from_translation(tile_pos.extend(-1.0)),
            ));
        }
    }
    
    // Create walls (just the perimeter for now)
    create_room_walls(commands, position, size);
    
    // Add room-specific elements
    match room_type {
        RoomType::Bridge => {
            // Add main terminal
            create_terminal(commands, position + Vec2::new(0.0, 50.0), true);
        }
        RoomType::Engineering => {
            // Add power console
            create_terminal(commands, position + Vec2::new(-100.0, 0.0), false);
            create_terminal(commands, position + Vec2::new(100.0, 0.0), false);
        }
        RoomType::Storage => {
            // Add storage containers (obstacles)
            create_obstacle(commands, position + Vec2::new(-50.0, 30.0));
            create_obstacle(commands, position + Vec2::new(50.0, -30.0));
        }
        _ => {}
    }
}

fn create_room_walls(commands: &mut Commands, position: Vec2, size: Vec2) {
    let half_size = size * 0.5;
    
    // Top wall
    for x in 0..((size.x / TILE_SIZE) as i32 + 1) {
        let wall_pos = position + Vec2::new(
            (x as f32) * TILE_SIZE - half_size.x,
            half_size.y,
        );
        spawn_wall(commands, wall_pos);
    }
    
    // Bottom wall
    for x in 0..((size.x / TILE_SIZE) as i32 + 1) {
        let wall_pos = position + Vec2::new(
            (x as f32) * TILE_SIZE - half_size.x,
            -half_size.y,
        );
        spawn_wall(commands, wall_pos);
    }
    
    // Left wall
    for y in 1..((size.y / TILE_SIZE) as i32) {
        let wall_pos = position + Vec2::new(
            -half_size.x,
            (y as f32) * TILE_SIZE - half_size.y,
        );
        spawn_wall(commands, wall_pos);
    }
    
    // Right wall
    for y in 1..((size.y / TILE_SIZE) as i32) {
        let wall_pos = position + Vec2::new(
            half_size.x,
            (y as f32) * TILE_SIZE - half_size.y,
        );
        spawn_wall(commands, wall_pos);
    }
}

fn spawn_wall(commands: &mut Commands, position: Vec2) {
    commands.spawn((
        Wall,
        SpaceshipLevel,
        Sprite {
            color: WALL_COLOR,
            custom_size: Some(Vec2::splat(TILE_SIZE)),
            ..default()
        },
        Transform::from_translation(position.extend(0.0)),
        // Avian2D physics
        RigidBody::Static,
        Collider::rectangle(TILE_SIZE, TILE_SIZE),
    ));
}

fn create_door(commands: &mut Commands, position: Vec2, connects: (RoomType, RoomType), locked: bool) {
    commands.spawn((
        Door { connects, locked },
        SpaceshipLevel,
        Sprite {
            color: if locked { Color::srgb(0.8, 0.2, 0.2) } else { DOOR_COLOR },
            custom_size: Some(Vec2::new(TILE_SIZE * 1.5, TILE_SIZE * 2.0)),
            ..default()
        },
        Transform::from_translation(position.extend(1.0)),
        // Avian2D physics - sensor for doors (no collision but detects overlap)
        RigidBody::Static,
        Collider::rectangle(TILE_SIZE * 1.5, TILE_SIZE * 2.0),
        Sensor,
    ));
}

fn create_terminal(commands: &mut Commands, position: Vec2, is_main: bool) {
    commands.spawn((
        crate::terminal::InteractableTerminal { is_main },
        SpaceshipLevel,
        Sprite {
            color: if is_main { Color::srgb(0.2, 0.8, 0.8) } else { Color::srgb(0.3, 0.5, 0.6) },
            custom_size: Some(Vec2::new(TILE_SIZE * 1.5, TILE_SIZE * 2.0)),
            ..default()
        },
        Transform::from_translation(position.extend(2.0)),
        // Avian2D physics - sensor for interaction
        RigidBody::Static,
        Collider::rectangle(TILE_SIZE * 1.5, TILE_SIZE * 2.0),
        Sensor,
    ));
}

fn create_obstacle(commands: &mut Commands, position: Vec2) {
    commands.spawn((
        Wall, // Reuse wall component for collision
        SpaceshipLevel,
        Sprite {
            color: Color::srgb(0.4, 0.3, 0.2),
            custom_size: Some(Vec2::new(TILE_SIZE * 2.0, TILE_SIZE * 1.5)),
            ..default()
        },
        Transform::from_translation(position.extend(0.0)),
        // Avian2D physics
        RigidBody::Static,
        Collider::rectangle(TILE_SIZE * 2.0, TILE_SIZE * 1.5),
    ));
}

fn update_room_visibility(
    current_room: Res<CurrentRoom>,
    mut room_query: Query<&mut Room>,
) {
    for mut room in room_query.iter_mut() {
        room.active = room.room_type == current_room.room_type;
    }
}

fn check_room_transitions(
    player_query: Query<&Transform, With<crate::player::Player>>,
    door_query: Query<(&Transform, &Door)>,
    mut current_room: ResMut<CurrentRoom>,
) {
    if let Ok(player_transform) = player_query.get_single() {
        let player_pos = player_transform.translation.truncate();
        
        for (door_transform, door) in door_query.iter() {
            if !door.locked {
                let door_pos = door_transform.translation.truncate();
                let distance = player_pos.distance(door_pos);
                
                if distance < TILE_SIZE {
                    // Transition to the other room
                    if current_room.room_type == door.connects.0 {
                        current_room.room_type = door.connects.1;
                    } else if current_room.room_type == door.connects.1 {
                        current_room.room_type = door.connects.0;
                    }
                }
            }
        }
    }
}

fn cleanup_spaceship_level(
    mut commands: Commands,
    level_query: Query<Entity, With<SpaceshipLevel>>,
) {
    for entity in level_query.iter() {
        commands.entity(entity).despawn_recursive();
    }
}