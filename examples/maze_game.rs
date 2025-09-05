use bevy::prelude::*;
use avian2d::prelude::*;
use rand::prelude::*;

// =====================================
// TUTORIAL: Complete Maze Game Example
// =====================================
// This example shows:
// 1. Component-based architecture (ECS)
// 2. Procedural maze generation
// 3. Physics and collision detection
// 4. Event-driven game logic
// 5. Resource management
// =====================================

fn main() {
    App::new()
        .add_plugins(DefaultPlugins.set(WindowPlugin {
            primary_window: Some(Window {
                title: "Maze Runner - Complete Tutorial".into(),
                resolution: (1280., 800.).into(),
                ..default()
            }),
            ..default()
        }))
        .add_plugins(PhysicsPlugins::default())
        // Resources - shared state
        .insert_resource(MazeState::default())
        // Events - communication between systems
        .add_event::<MazeCompletedEvent>()
        // Systems - game logic
        .add_systems(Startup, setup_world)
        .add_systems(Update, (
            player_movement,
            camera_follow,
            check_maze_entry,
            check_maze_completion,
            handle_maze_completed,
            debug_controls,
        ))
        .run();
}

// ====================
// COMPONENTS - What things ARE
// ====================
#[derive(Component)]
struct Player;

#[derive(Component)]
struct MazeWall;

#[derive(Component)]
struct MazeFloor; 

#[derive(Component)]
struct MazeGoal;

#[derive(Component)]
struct MazeEntity;  // Marks all maze parts for easy cleanup

#[derive(Component)]
struct MainRoom;

// ====================
// RESOURCES - Shared game state
// ====================
#[derive(Resource)]
struct MazeState {
    in_maze: bool,
    current_seed: u64,
    completions: u32,
}

impl Default for MazeState {
    fn default() -> Self {
        Self {
            in_maze: false,
            current_seed: random(),
            completions: 0,
        }
    }
}

// ====================
// EVENTS - Messages between systems
// ====================
#[derive(Event)]
struct MazeCompletedEvent;

// ====================
// CONSTANTS - Game configuration
// ====================
const CELL_SIZE: f32 = 35.0;
const MAZE_WIDTH: usize = 19;
const MAZE_HEIGHT: usize = 15;

// ====================
// SETUP - Initialize the game world
// ====================
fn setup_world(mut commands: Commands) {
    println!("\n╔════════════════════════════════════╗");
    println!("║      MAZE RUNNER - TUTORIAL       ║");
    println!("╠════════════════════════════════════╣");
    println!("║ CONTROLS:                          ║");
    println!("║ • Arrow Keys/WASD: Move            ║");
    println!("║ • R: Reset to start                ║");
    println!("║ • Space: Show position             ║");
    println!("╠════════════════════════════════════╣");
    println!("║ OBJECTIVE:                         ║");
    println!("║ 1. Go RIGHT to find the maze →     ║");
    println!("║ 2. Navigate to the GREEN goal      ║");
    println!("║ 3. Each completion = new maze!     ║");
    println!("╚════════════════════════════════════╝\n");
    
    // Camera
    commands.spawn(Camera2d::default());
    
    // Main room
    spawn_main_room(&mut commands);
    
    // Hallway
    spawn_hallway(&mut commands);
    
    // Player - spawn in center of main room
    commands.spawn((
        Player,
        Sprite {
            color: Color::srgb(0.3, 0.6, 1.0),
            custom_size: Some(Vec2::splat(20.0)),
            ..default()
        },
        Transform::from_xyz(-100.0, 0.0, 1.0),  // Spawn further left in room
        RigidBody::Dynamic,
        Collider::circle(10.0),
        LinearVelocity::default(),
        LockedAxes::ROTATION_LOCKED,
        LinearDamping(10.0),
        GravityScale(0.0),
    ));
}

fn spawn_main_room(commands: &mut Commands) {
    // Floor
    commands.spawn((
        MainRoom,
        Sprite {
            color: Color::srgb(0.1, 0.1, 0.2),
            custom_size: Some(Vec2::new(600.0, 500.0)),
            ..default()
        },
        Transform::from_xyz(0.0, 0.0, -10.0),
    ));
    
    // Walls with door opening
    let walls = [
        (0.0, 260.0, 620.0, 20.0),     // Top
        (0.0, -260.0, 620.0, 20.0),    // Bottom
        (-310.0, 0.0, 20.0, 500.0),    // Left
        (310.0, 130.0, 20.0, 240.0),   // Right top
        (310.0, -130.0, 20.0, 240.0),  // Right bottom
    ];
    
    for (x, y, w, h) in walls {
        commands.spawn((
            MainRoom,
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
}

fn spawn_hallway(commands: &mut Commands) {
    // Hallway floor
    commands.spawn((
        Sprite {
            color: Color::srgb(0.12, 0.10, 0.18),
            custom_size: Some(Vec2::new(300.0, 60.0)),
            ..default()
        },
        Transform::from_xyz(450.0, 0.0, -9.0),
    ));
    
    // Hallway walls
    commands.spawn((
        Sprite {
            color: Color::srgb(0.05, 0.05, 0.12),
            custom_size: Some(Vec2::new(300.0, 5.0)),
            ..default()
        },
        Transform::from_xyz(450.0, 32.5, -5.0),
        RigidBody::Static,
        Collider::rectangle(300.0, 5.0),
    ));
    
    commands.spawn((
        Sprite {
            color: Color::srgb(0.05, 0.05, 0.12),
            custom_size: Some(Vec2::new(300.0, 5.0)),
            ..default()
        },
        Transform::from_xyz(450.0, -32.5, -5.0),
        RigidBody::Static,
        Collider::rectangle(300.0, 5.0),
    ));
}

// ====================
// MAZE GENERATION - Recursive Backtracking Algorithm
// ====================
fn generate_maze(commands: &mut Commands, seed: u64) {
    // This is a classic maze generation algorithm!
    let mut rng = StdRng::seed_from_u64(seed);
    let mut grid = vec![vec![true; MAZE_WIDTH]; MAZE_HEIGHT]; // true = wall
    
    // Start from position (1,1)
    let mut stack = vec![(1usize, 1usize)];
    grid[1][1] = false; // Mark as path
    
    // Recursive backtracking
    while !stack.is_empty() {
        let (cx, cy) = *stack.last().unwrap();
        
        // Find unvisited neighbors
        let mut neighbors = Vec::new();
        for (dx, dy) in [(0, -2i32), (2, 0), (0, 2), (-2, 0)] {
            let nx = (cx as i32 + dx) as usize;
            let ny = (cy as i32 + dy) as usize;
            
            if nx > 0 && nx < MAZE_WIDTH - 1 && ny > 0 && ny < MAZE_HEIGHT - 1 {
                if grid[ny][nx] {  // If still a wall (unvisited)
                    neighbors.push((nx, ny, dx, dy));
                }
            }
        }
        
        if !neighbors.is_empty() {
            // Choose random neighbor
            let &(nx, ny, dx, dy) = neighbors.choose(&mut rng).unwrap();
            
            // Carve path to neighbor
            grid[ny][nx] = false;
            grid[(cy as i32 + dy/2) as usize][(cx as i32 + dx/2) as usize] = false;
            
            stack.push((nx, ny));
        } else {
            stack.pop(); // Backtrack
        }
    }
    
    // Spawn maze entities
    let offset = Vec2::new(700.0, 200.0);
    for y in 0..MAZE_HEIGHT {
        for x in 0..MAZE_WIDTH {
            let pos = Vec2::new(
                x as f32 * CELL_SIZE + offset.x,
                -(y as f32 * CELL_SIZE) + offset.y,
            );
            
            if grid[y][x] {
                // Wall
                commands.spawn((
                    MazeEntity,
                    MazeWall,
                    Sprite {
                        color: Color::srgb(0.02, 0.02, 0.06),
                        custom_size: Some(Vec2::splat(CELL_SIZE)),
                        ..default()
                    },
                    Transform::from_xyz(pos.x, pos.y, -5.0),
                    RigidBody::Static,
                    Collider::rectangle(CELL_SIZE, CELL_SIZE),
                ));
            } else {
                // Path
                commands.spawn((
                    MazeEntity,
                    MazeFloor,
                    Sprite {
                        color: Color::srgb(0.15, 0.12, 0.25),
                        custom_size: Some(Vec2::splat(CELL_SIZE - 2.0)),
                        ..default()
                    },
                    Transform::from_xyz(pos.x, pos.y, -10.0),
                ));
            }
        }
    }
    
    // Goal at bottom-right
    let goal_pos = Vec2::new(
        (MAZE_WIDTH - 2) as f32 * CELL_SIZE + offset.x,
        -((MAZE_HEIGHT - 2) as f32 * CELL_SIZE) + offset.y,
    );
    
    commands.spawn((
        MazeEntity,
        MazeGoal,
        Sprite {
            color: Color::srgb(0.3, 1.0, 0.3),
            custom_size: Some(Vec2::splat(CELL_SIZE * 0.7)),
            ..default()
        },
        Transform::from_xyz(goal_pos.x, goal_pos.y, -8.0),
    ));
}

fn clear_maze(commands: &mut Commands, maze_query: &Query<Entity, With<MazeEntity>>) {
    for entity in maze_query.iter() {
        commands.entity(entity).despawn();
    }
}

// ====================
// GAME SYSTEMS - Update logic
// ====================
fn player_movement(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut query: Query<&mut LinearVelocity, With<Player>>,
) {
    if let Ok(mut velocity) = query.get_single_mut() {
        let mut dir = Vec2::ZERO;
        
        if keyboard.pressed(KeyCode::ArrowUp) || keyboard.pressed(KeyCode::KeyW) { 
            dir.y += 1.0; 
        }
        if keyboard.pressed(KeyCode::ArrowDown) || keyboard.pressed(KeyCode::KeyS) { 
            dir.y -= 1.0; 
        }
        if keyboard.pressed(KeyCode::ArrowLeft) || keyboard.pressed(KeyCode::KeyA) { 
            dir.x -= 1.0; 
        }
        if keyboard.pressed(KeyCode::ArrowRight) || keyboard.pressed(KeyCode::KeyD) { 
            dir.x += 1.0; 
        }
        
        velocity.0 = if dir.length() > 0.0 {
            dir.normalize() * 250.0
        } else {
            velocity.0 * 0.9
        };
    }
}

fn camera_follow(
    player: Query<&Transform, (With<Player>, Without<Camera2d>)>,
    mut camera: Query<&mut Transform, With<Camera2d>>,
) {
    if let (Ok(p), Ok(mut c)) = (player.get_single(), camera.get_single_mut()) {
        let target = if p.translation.x > 500.0 {
            // In maze - offset camera
            Vec3::new(p.translation.x * 0.5 + 150.0, p.translation.y * 0.5, c.translation.z)
        } else {
            // In room - center camera
            Vec3::new(p.translation.x * 0.3, p.translation.y * 0.3, c.translation.z)
        };
        c.translation = c.translation.lerp(target, 0.1);
    }
}

fn check_maze_entry(
    player: Query<&Transform, With<Player>>,
    mut maze_state: ResMut<MazeState>,
    mut commands: Commands,
    maze_query: Query<Entity, With<MazeEntity>>,
) {
    if let Ok(pos) = player.get_single() {
        let should_be_in_maze = pos.translation.x > 600.0;
        
        if should_be_in_maze && !maze_state.in_maze {
            // Entering maze
            maze_state.in_maze = true;
            clear_maze(&mut commands, &maze_query);
            generate_maze(&mut commands, maze_state.current_seed);
            println!("➡️ Entered Maze #{}", maze_state.completions + 1);
        } else if !should_be_in_maze && maze_state.in_maze {
            // Leaving maze
            maze_state.in_maze = false;
            clear_maze(&mut commands, &maze_query);
            println!("⬅️ Returned to Main Room");
        }
    }
}

fn check_maze_completion(
    player: Query<&Transform, With<Player>>,
    goal: Query<&Transform, With<MazeGoal>>,
    maze_state: Res<MazeState>,
    mut events: EventWriter<MazeCompletedEvent>,
) {
    if !maze_state.in_maze { return; }
    
    if let (Ok(p), Ok(g)) = (player.get_single(), goal.get_single()) {
        let distance = p.translation.truncate().distance(g.translation.truncate());
        if distance < CELL_SIZE * 0.5 {
            events.send(MazeCompletedEvent);
        }
    }
}

fn handle_maze_completed(
    mut events: EventReader<MazeCompletedEvent>,
    mut maze_state: ResMut<MazeState>,
    mut player: Query<&mut Transform, With<Player>>,
    mut commands: Commands,
    maze_query: Query<Entity, With<MazeEntity>>,
) {
    for _ in events.read() {
        maze_state.completions += 1;
        maze_state.current_seed = random();
        
        println!("🎉 MAZE COMPLETED! (Total: {})", maze_state.completions);
        println!("   Generating new maze...");
        
        // Reset player
        if let Ok(mut transform) = player.get_single_mut() {
            transform.translation = Vec3::new(350.0, 0.0, 1.0);
        }
        
        // Generate new maze
        clear_maze(&mut commands, &maze_query);
        generate_maze(&mut commands, maze_state.current_seed);
    }
}

fn debug_controls(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut player: Query<&mut Transform, With<Player>>,
) {
    if let Ok(mut transform) = player.get_single_mut() {
        if keyboard.just_pressed(KeyCode::KeyR) {
            transform.translation = Vec3::new(-100.0, 0.0, 1.0);
            println!("🔄 Reset to start position in main room");
        }
        if keyboard.just_pressed(KeyCode::Space) {
            println!("📍 Position: ({:.0}, {:.0})", 
                transform.translation.x, 
                transform.translation.y
            );
        }
    }
}