# Maze Generation Tutorial - Learning Rust & Bevy

## Overview
This tutorial explains the procedural maze system we built for Runetika, demonstrating key concepts in Rust, Bevy, and game development.

## Key Learning Concepts

### 1. **Entity Component System (ECS)**
Bevy uses ECS architecture where:
- **Entities**: Game objects (player, walls, floors)
- **Components**: Data attached to entities (`Player`, `MazeWall`, `Transform`)
- **Systems**: Functions that process entities with specific components
- **Resources**: Shared game state (`MazeState`)

### 2. **Procedural Generation with Recursive Backtracking**
The maze uses a classic algorithm:
```rust
// Start with a grid of walls
let mut maze = vec![vec![Cell::Wall; WIDTH]; HEIGHT];

// Carve paths using a stack
let mut stack = vec![(1, 1)];
while !stack.is_empty() {
    // Find unvisited neighbors
    // Choose random neighbor
    // Carve path to it
    // Either continue or backtrack
}
```

### 3. **Component Markers**
We use empty structs as markers to identify entities:
```rust
#[derive(Component)]
struct Player;       // Marks the player entity
#[derive(Component)]
struct MazeWall;     // Marks wall entities
#[derive(Component)]
struct MazeGoal;     // Marks the goal
```

### 4. **State Management**
The `MazeState` resource tracks:
- Whether player is in the maze
- Current maze seed for regeneration
- Number of completions

### 5. **Event-Driven Architecture**
Systems communicate through events:
```rust
#[derive(Event)]
struct MazeCompletedEvent;

// System sends event
events.send(MazeCompletedEvent);

// Another system handles it
for _ in events.read() {
    // Regenerate maze
}
```

## File Structure

### `examples/maze_game.rs` - Complete Tutorial
Standalone example with everything in one file:
- Setup systems
- Maze generation algorithm
- Movement and physics
- Event handling
- Debug controls

### `src/maze.rs` - Modular Plugin
Reusable maze module that can be added to any Bevy app:
```rust
app.add_plugins(MazePlugin);
```

### `examples/room_with_maze.rs` - Integration Example
Shows how to integrate the maze module with existing game.

## How the Maze Works

### 1. **Room Layout**
```
[Main Room] --[Hallway]-- [Maze Area]
     ↑                          ↑
   Player                    Generated
   Spawns                   Procedurally
```

### 2. **Boundary Detection**
```rust
// Check player position
if player.x > 600.0 && !in_maze {
    // Enter maze - generate new one
} else if player.x < 600.0 && in_maze {
    // Exit maze - clear it
}
```

### 3. **Maze Generation Process**
1. Clear any existing maze entities
2. Generate new maze with random seed
3. Spawn wall and floor sprites
4. Add physics colliders to walls
5. Place goal in bottom-right

### 4. **Completion Flow**
1. Player reaches goal (distance check)
2. Send `MazeCompletedEvent`
3. Increment completion counter
4. Teleport player back to hallway
5. Generate new maze with new seed

## Rust Concepts Demonstrated

### Ownership & Borrowing
```rust
// Mutable borrow for modification
fn movement(mut query: Query<&mut LinearVelocity, With<Player>>) {
    for mut velocity in &mut query {
        velocity.0 = new_velocity;
    }
}

// Immutable borrow for reading
fn check_position(query: Query<&Transform, With<Player>>) {
    if let Ok(transform) = query.get_single() {
        // Read position
    }
}
```

### Pattern Matching
```rust
match cell {
    Cell::Wall => { /* spawn wall */ },
    Cell::Path => { /* spawn floor */ },
    Cell::Goal => { /* spawn goal */ },
    _ => { /* handle other cases */ }
}
```

### Iterators & Functional Programming
```rust
// Choose random neighbor
let neighbor = neighbors
    .choose(&mut rng)
    .unwrap();

// Filter and collect
let walls: Vec<_> = maze_query
    .iter()
    .filter(|e| /* condition */)
    .collect();
```

### Error Handling
```rust
// Using Result type
if let Ok(transform) = query.get_single() {
    // Handle success
}

// Early return on error
let player = query.get_single()?;
```

## Bevy Concepts Demonstrated

### System Scheduling
```rust
app.add_systems(Startup, setup_world)
   .add_systems(Update, (
       player_movement,
       camera_follow,
       check_maze_completion,
   ));
```

### Queries with Filters
```rust
// Query entities with Player component but without Camera2d
Query<&Transform, (With<Player>, Without<Camera2d>)>

// Query all maze entities
Query<Entity, With<MazeEntity>>
```

### Physics Integration (Avian2D)
```rust
commands.spawn((
    RigidBody::Dynamic,      // Can move
    Collider::circle(10.0),  // Circular collision
    LinearVelocity::default(), // Velocity component
    LinearDamping(10.0),     // Friction
));
```

### Camera Following
```rust
// Smooth camera lerp
camera.translation = camera.translation.lerp(target, 0.1);

// Different behavior based on location
let target = if player.x > 500.0 {
    // In maze - offset camera
} else {
    // In room - center camera
};
```

## Performance Considerations

### Entity Cleanup
Always despawn entities when not needed:
```rust
fn clear_maze(commands: &mut Commands, query: Query<Entity, With<MazeEntity>>) {
    for entity in query.iter() {
        commands.entity(entity).despawn();
    }
}
```

### Efficient Queries
Use specific queries to minimize iteration:
```rust
// Good: Specific query
Query<&Transform, With<Player>>

// Bad: Too broad
Query<&Transform>
```

### Resource Access
Use `Res` for read-only, `ResMut` for modifications:
```rust
fn read_state(state: Res<MazeState>) { }
fn modify_state(mut state: ResMut<MazeState>) { }
```

## Testing the System

Run the complete tutorial:
```bash
cargo run --example maze_game
```

### Controls
- **Arrow Keys/WASD**: Move the player
- **R**: Reset to starting position
- **Space**: Print current position
- **ESC**: Exit game

### What to Test
1. Movement in main room (collision with walls)
2. Entering hallway (visual transition)
3. Maze generation (random each time)
4. Goal detection (green square)
5. Respawn and regeneration

## Common Issues & Solutions

### Issue: Player gets stuck
**Solution**: Check collider sizes and LinearDamping value

### Issue: Maze not generating
**Solution**: Verify player position threshold (x > 600.0)

### Issue: Can't reach goal
**Solution**: Maze algorithm guarantees path exists from (1,1) to (WIDTH-2, HEIGHT-2)

### Issue: Performance drops
**Solution**: Ensure old maze entities are despawned before generating new ones

## Next Steps

### Enhancements You Could Add
1. **Multiple maze algorithms** (Prim's, Kruskal's)
2. **Maze difficulty levels** (size, complexity)
3. **Timer and scoring system**
4. **Collectibles in the maze**
5. **Enemies or obstacles**
6. **Mini-map display**
7. **Save/load maze seeds**
8. **Multiplayer racing**

### Learning Exercises
1. **Change maze size**: Modify `MAZE_WIDTH` and `MAZE_HEIGHT`
2. **Add sound effects**: Play sounds on entry/completion
3. **Visual improvements**: Add particle effects, animations
4. **New maze types**: Create spiral or circular mazes
5. **Path highlighting**: Show shortest path to goal

## Conclusion

This maze system demonstrates:
- Modular game design with ECS
- Procedural content generation
- Physics-based movement
- Event-driven architecture
- Rust ownership and safety
- Bevy's powerful abstractions

The code is structured to be both educational and production-ready, showing best practices for game development in Rust with Bevy.