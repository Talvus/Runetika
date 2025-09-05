use bevy::prelude::*;
use avian2d::prelude::*;
use rand::prelude::*;

pub struct MazePlugin;

impl Plugin for MazePlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(MazeState::default())
            .add_event::<MazeCompletedEvent>()
            .add_systems(Update, (
                check_maze_entry,
                check_maze_completion,
                handle_maze_completed,
            ));
    }
}

#[derive(Component)]
pub struct MazeWall;

#[derive(Component)]
pub struct MazeFloor;

#[derive(Component)]
pub struct MazeGoal;

#[derive(Component)]
pub struct MazeEntity;

#[derive(Component)]
pub struct Hallway;

#[derive(Resource, Default)]
pub struct MazeState {
    pub in_maze: bool,
    pub maze_seed: u64,
    pub completions: u32,
}

#[derive(Event)]
pub struct MazeCompletedEvent;

const CELL_SIZE: f32 = 40.0;
const WALL_THICKNESS: f32 = 5.0;
const MAZE_WIDTH: usize = 15;
const MAZE_HEIGHT: usize = 15;

#[derive(Clone, Copy, PartialEq)]
enum Cell {
    Wall,
    Path,
    Start,
    Goal,
}

pub fn spawn_hallway(commands: &mut Commands) -> Vec2 {
    let hallway_start = Vec2::new(400.0, 0.0); // Right side of main room
    let hallway_end = Vec2::new(800.0, 0.0);   // Entrance to maze
    
    // Hallway floor
    commands.spawn((
        Hallway,
        Sprite {
            color: Color::srgb(0.12, 0.10, 0.18),
            custom_size: Some(Vec2::new(400.0, 80.0)),
            ..default()
        },
        Transform::from_xyz(600.0, 0.0, -9.0),
    ));
    
    // Hallway walls
    for (x, y, w, h) in [
        (600.0, 50.0, 400.0, WALL_THICKNESS),  // Top wall
        (600.0, -50.0, 400.0, WALL_THICKNESS), // Bottom wall
    ] {
        commands.spawn((
            Hallway,
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
    
    // Door indicators
    commands.spawn((
        Hallway,
        Sprite {
            color: Color::srgba(0.5, 0.8, 0.3, 0.3),
            custom_size: Some(Vec2::new(20.0, 60.0)),
            ..default()
        },
        Transform::from_xyz(410.0, 0.0, -8.0),
    ));
    
    commands.spawn((
        Hallway,
        Text::new("→ MAZE"),
        TextFont {
            font_size: 16.0,
            ..default()
        },
        Node {
            position_type: PositionType::Absolute,
            left: Val::Px(550.0),
            top: Val::Px(380.0),
            ..default()
        },
    ));
    
    hallway_end
}

pub fn generate_maze(commands: &mut Commands, seed: u64, offset: Vec2) {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut maze = vec![vec![Cell::Wall; MAZE_WIDTH]; MAZE_HEIGHT];
    
    // Generate maze using recursive backtracking
    let mut stack = vec![(1, 1)];
    maze[1][1] = Cell::Path;
    
    while !stack.is_empty() {
        let (cx, cy) = *stack.last().unwrap();
        let mut neighbors = Vec::new();
        
        // Check all four directions
        for (dx, dy) in [(0, -2), (2, 0), (0, 2), (-2, 0)] {
            let nx = cx as i32 + dx;
            let ny = cy as i32 + dy;
            
            if nx > 0 && nx < MAZE_WIDTH as i32 - 1 
                && ny > 0 && ny < MAZE_HEIGHT as i32 - 1 {
                let nx = nx as usize;
                let ny = ny as usize;
                if maze[ny][nx] == Cell::Wall {
                    neighbors.push((nx, ny, dx, dy));
                }
            }
        }
        
        if !neighbors.is_empty() {
            let (nx, ny, dx, dy) = neighbors.choose(&mut rng).unwrap().clone();
            
            // Carve path to neighbor
            maze[ny][nx] = Cell::Path;
            maze[(cy as i32 + dy/2) as usize][(cx as i32 + dx/2) as usize] = Cell::Path;
            
            stack.push((nx, ny));
        } else {
            stack.pop();
        }
    }
    
    // Set start and goal
    maze[1][1] = Cell::Start;
    maze[MAZE_HEIGHT - 2][MAZE_WIDTH - 2] = Cell::Goal;
    
    // Spawn maze entities
    for (y, row) in maze.iter().enumerate() {
        for (x, &cell) in row.iter().enumerate() {
            let world_pos = Vec2::new(
                x as f32 * CELL_SIZE + offset.x,
                -(y as f32 * CELL_SIZE) + offset.y,
            );
            
            match cell {
                Cell::Wall => {
                    commands.spawn((
                        MazeEntity,
                        MazeWall,
                        Sprite {
                            color: Color::srgb(0.02, 0.02, 0.06),
                            custom_size: Some(Vec2::splat(CELL_SIZE)),
                            ..default()
                        },
                        Transform::from_xyz(world_pos.x, world_pos.y, -5.0),
                        RigidBody::Static,
                        Collider::rectangle(CELL_SIZE, CELL_SIZE),
                    ));
                }
                Cell::Path | Cell::Start => {
                    commands.spawn((
                        MazeEntity,
                        MazeFloor,
                        Sprite {
                            color: Color::srgb(0.15, 0.12, 0.25),
                            custom_size: Some(Vec2::splat(CELL_SIZE - 2.0)),
                            ..default()
                        },
                        Transform::from_xyz(world_pos.x, world_pos.y, -10.0),
                    ));
                }
                Cell::Goal => {
                    // Floor under goal
                    commands.spawn((
                        MazeEntity,
                        MazeFloor,
                        Sprite {
                            color: Color::srgb(0.15, 0.12, 0.25),
                            custom_size: Some(Vec2::splat(CELL_SIZE - 2.0)),
                            ..default()
                        },
                        Transform::from_xyz(world_pos.x, world_pos.y, -10.0),
                    ));
                    
                    // Goal marker
                    commands.spawn((
                        MazeEntity,
                        MazeGoal,
                        Sprite {
                            color: Color::srgba(0.3, 1.0, 0.3, 0.8),
                            custom_size: Some(Vec2::splat(CELL_SIZE * 0.6)),
                            ..default()
                        },
                        Transform::from_xyz(world_pos.x, world_pos.y, -8.0),
                    ));
                }
            }
        }
    }
    
    // Add exit back to hallway
    commands.spawn((
        MazeEntity,
        Sprite {
            color: Color::srgba(0.8, 0.5, 0.3, 0.3),
            custom_size: Some(Vec2::new(60.0, 20.0)),
            ..default()
        },
        Transform::from_xyz(offset.x + CELL_SIZE, offset.y, -8.0),
    ));
}

pub fn clear_maze(commands: &mut Commands, maze_query: Query<Entity, With<MazeEntity>>) {
    for entity in maze_query.iter() {
        commands.entity(entity).despawn();
    }
}

fn check_maze_entry(
    player_query: Query<&Transform, With<crate::main_room::Player>>,
    mut maze_state: ResMut<MazeState>,
    mut commands: Commands,
    maze_query: Query<Entity, With<MazeEntity>>,
) {
    if let Ok(player_pos) = player_query.get_single() {
        let in_hallway = player_pos.translation.x > 400.0 
            && player_pos.translation.x < 800.0
            && player_pos.translation.y.abs() < 40.0;
        
        let in_maze_area = player_pos.translation.x > 800.0;
        
        if in_maze_area && !maze_state.in_maze {
            // Enter maze
            maze_state.in_maze = true;
            maze_state.maze_seed = rand::thread_rng().gen();
            
            // Clear old maze if exists
            clear_maze(&mut commands, maze_query);
            
            // Generate new maze
            let maze_offset = Vec2::new(850.0, 200.0);
            generate_maze(&mut commands, maze_state.maze_seed, maze_offset);
            
            println!("Entered maze #{} (seed: {})", maze_state.completions + 1, maze_state.maze_seed);
        } else if !in_hallway && !in_maze_area && maze_state.in_maze {
            // Left maze area
            maze_state.in_maze = false;
            clear_maze(&mut commands, maze_query);
            println!("Returned to main room");
        }
    }
}

fn check_maze_completion(
    player_query: Query<&Transform, With<crate::main_room::Player>>,
    goal_query: Query<&Transform, With<MazeGoal>>,
    maze_state: Res<MazeState>,
    mut events: EventWriter<MazeCompletedEvent>,
) {
    if !maze_state.in_maze {
        return;
    }
    
    if let (Ok(player_pos), Ok(goal_pos)) = (player_query.get_single(), goal_query.get_single()) {
        let distance = player_pos.translation.truncate().distance(goal_pos.translation.truncate());
        
        if distance < CELL_SIZE * 0.5 {
            events.send(MazeCompletedEvent);
        }
    }
}

fn handle_maze_completed(
    mut events: EventReader<MazeCompletedEvent>,
    mut maze_state: ResMut<MazeState>,
    mut player_query: Query<&mut Transform, With<crate::main_room::Player>>,
    mut commands: Commands,
    maze_query: Query<Entity, With<MazeEntity>>,
) {
    for _ in events.read() {
        maze_state.completions += 1;
        println!("🎉 Maze completed! Total completions: {}", maze_state.completions);
        
        // Teleport player back to start of hallway
        if let Ok(mut player_transform) = player_query.get_single_mut() {
            player_transform.translation = Vec3::new(450.0, 0.0, 1.0);
        }
        
        // Clear current maze
        clear_maze(&mut commands, maze_query);
        
        // Generate new maze immediately
        maze_state.maze_seed = rand::thread_rng().gen();
        let maze_offset = Vec2::new(850.0, 200.0);
        generate_maze(&mut commands, maze_state.maze_seed, maze_offset);
        
        println!("New maze generated! (seed: {})", maze_state.maze_seed);
    }
}