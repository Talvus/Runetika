# WARP.md

This file provides guidance to WARP (warp.dev) when working with code in this repository.

## Project Overview

Runetika is a top-down RPG prototype built with Bevy 0.13 game engine and Avian2D 0.1 physics engine. The game centers on a fallen silicon-based civilization with mystical realism themes, featuring glyphs, puzzles, and mazes.

## Common Commands

```bash
# Build the project
cargo build

# Run the game
cargo run

# Check for compilation errors without building
cargo check

# Run tests
cargo test

# Run a specific test
cargo test test_name

# Format code
cargo fmt

# Check formatting without modifying files
cargo fmt -- --check

# Run linter
cargo clippy

# Run linter with warnings as errors
cargo clippy -- -D warnings

# Build optimized release version
cargo build --release

# Run optimized release version
cargo run --release

# Clean build artifacts
cargo clean
```

## Project Architecture

### Core Structure
- **Entry Point**: `src/main.rs` - Single file containing all game logic currently
- **Game Engine**: Bevy 0.13 with Entity Component System (ECS) architecture
- **Physics**: Avian2D 0.1 for 2D physics and collision detection

### Current Components & Systems

#### Components
- `Tile`: Marker component for map tiles

#### Resources
- `MapSize`: Stores map dimensions (width: 10, height: 10)

#### Systems
- `setup_map`: Startup system that:
  - Creates a 10x10 grid of tiles
  - Each tile is 32x32 world units with 30x30 visual size
  - Tiles are dark green sprites
  - Spawns tiles using Bevy's Commands API

### Window Configuration
- Title: "Runetika"
- Resolution: 640x480 pixels
- Configured via `WindowPlugin` in the Bevy app builder

## Development Notes

### Modifying the Map
To change map size, edit the `MapSize` resource in `setup_map()`:
```rust
let map = MapSize { width: 20, height: 15 };  // Example: 20x15 grid
```

To change tile appearance, modify the `Sprite` component:
```rust
sprite: Sprite { 
    color: Color::DARK_GREEN,  // Change color here
    custom_size: Some(Vec2::splat(30.0)),  // Change size here
    ..Default::default() 
}
```

### Adding New Features
When implementing game features, follow Bevy's ECS patterns:
1. Define components with `#[derive(Component)]`
2. Define resources with `#[derive(Resource)]`
3. Create systems as functions taking Query/Commands parameters
4. Register systems with `.add_systems()` in the app builder

### Dependencies
The project requires internet connection for initial build to fetch dependencies from crates.io:
- `bevy = "0.13"` - Game engine
- `avian2d = "0.1"` - 2D physics engine

### Future Development Areas
Based on the game concept, these systems will need implementation:
- Puzzle mechanics (potentially ARC-style puzzles)
- Glyph system for mystical elements
- Maze generation and navigation
- Silicon-based entity interactions
- Progress tracking and goal systems
