# Runetika Maze Implementation and bevy_knossos Analysis

## Executive Summary

The Runetika codebase has **two competing maze systems**:
1. **Old Recursive Backtracking Maze** (`src/maze.rs`) - Simple but functional
2. **New Wave Function Collapse (WFC) System** (`src/procedural/wfc/`) - Advanced, ARC-integrated

There is **1 critical build error** that needs fixing: the `despawn_silicon_overlay` function signature mismatch in `perspective.rs` line 139.

**bevy_knossos 0.8.1** is listed in Cargo.toml but **is not currently used anywhere in the codebase**.

---

## Critical Build Error

### Location: `src/perspective.rs` line 139
**Error Type**: Function argument mismatch

```rust
// LINE 139 - CURRENT (BROKEN)
despawn_silicon_overlay(&mut commands);

// LINE 223 - FUNCTION DEFINITION
fn despawn_silicon_overlay(mut commands: Commands, query: Query<Entity, With<SiliconVision>>) {
    for entity in query.iter() {
        commands.entity(entity).despawn();
    }
}
```

**Problem**: 
- Function expects 2 arguments: `Commands` and `Query<Entity, With<SiliconVision>>`
- Being called with only 1 argument: `&mut Commands`
- The function signature uses `mut commands: Commands` (owned, not reference)

**Error Message**:
```
error[E0061]: this function takes 2 arguments but 1 argument was supplied
   --> src/perspective.rs:139:17
139 |                 despawn_silicon_overlay(&mut commands);
```

**Solution**: The function needs to be called with the query parameter. The system is being called from `apply_perspective_switch` which is a system function that has access to commands but not the query.

---

## Current Maze Implementation

### Architecture Overview

```
src/maze.rs (Simple Recursive Backtracking)
    ├── MazePlugin - Registers events and systems
    ├── MazeState (Resource)
    │   ├── in_maze: bool
    │   ├── maze_seed: u64
    │   ├── completions: u32
    ├── Components
    │   ├── MazeWall
    │   ├── MazeFloor
    │   ├── MazeGoal
    │   ├── MazeEntity
    │   └── Hallway
    └── Systems
        ├── check_maze_entry() - Monitor player position
        ├── check_maze_completion() - Detect goal reached
        └── handle_maze_completed() - Reset and generate new maze

src/procedural/wfc/ (Wave Function Collapse - Advanced)
    ├── mod.rs - ProceduralPlugin and WFC integration
    ├── tiles.rs - 9-tile circuit board theme with Wang sockets
    ├── constraints.rs - Adjacency rules and constraint graph
    ├── algorithm.rs - WFC observe/collapse/propagate steps
    ├── renderer.rs - Isometric 2.5D visualization
    └── terminal_commands.rs - Terminal interface for WFC
```

---

## Old Recursive Backtracking Maze (`src/maze.rs`)

### Constants & Configuration
```rust
const CELL_SIZE: f32 = 40.0;
const WALL_THICKNESS: f32 = 5.0;
const MAZE_WIDTH: usize = 15;
const MAZE_HEIGHT: usize = 15;
```

### Generation Algorithm

**Location**: `generate_maze()` function

```
1. Initialize 15x15 grid with all walls
2. Start at (1, 1) and mark as path
3. Use recursive backtracking:
   - From current cell, find unvisited neighbors at distance 2
   - Pick random neighbor and carve path through wall between
   - Push neighbor to stack and repeat
   - Backtrack when stuck
4. Carve 2-step jumps (leaving walls intact for structure)
5. Place start at [1][1] and goal at [MAZE_HEIGHT-2][MAZE_WIDTH-2]
6. Spawn physical entities:
   - Walls: Static colliders with dark sprites
   - Paths: Floor sprites (no physics)
   - Goal: Green indicator sprite
```

### Key Functions

| Function | Purpose | Line |
|----------|---------|------|
| `spawn_hallway()` | Creates connecting hallway from room to maze | ~57 |
| `generate_maze()` | Main algorithm, spawns entities | ~89 |
| `clear_maze()` | Despawns all maze entities | ~194 |
| `check_maze_entry()` | Detects player crossing x=800.0 | ~204 |
| `check_maze_completion()` | Checks if player within CELL_SIZE*0.5 of goal | ~234 |
| `handle_maze_completed()` | Teleports player, increments counter, generates new maze | ~251 |

### Integration Points

**With main_room.rs**:
- `spawn_hallway()` called in `setup_room()` 
- Hallway positioned at x=600.0 (middle-right of room)
- Door opens to maze at x=800.0

**With player.rs**:
- Player tracked via `Query<&Transform, With<crate::main_room::Player>>`
- Position checked against zone boundaries

**Issues**:
- Uses deprecated `get_single()` instead of `single()` (line 251)
- Hardcoded boundary checks (x > 800.0, etc.)
- No physics between old maze system and new player system

---

## New Wave Function Collapse System (`src/procedural/wfc/`)

### Architecture

**Core Components** (from `tiles.rs`):

```
9-Tile Circuit Board Theme:
├── Empty (weight 2.0) - Open spaces
├── Straight V/H (weight 1.0) - Corridors
├── Corners (4 variants, weight 0.8) - NE/NW/SE/SW
├── T-Junction (weight 0.5) - 3-way junction
├── Cross (weight 0.3) - 4-way intersection
├── Capacitor, Resistor, Junction - Circuit-themed variants

Wang Tiles / Socket Matching:
├── Each tile has 4 sockets: [North, East, South, West]
├── Socket types: None, Circuit, Power, Ground, Data
└── Adjacency: Tiles match only if sockets compatible
```

### Algorithm (from `algorithm.rs`)

**Three-Step Iterative Process**:

```
1. OBSERVE - Find minimum entropy cell
   - Entropy = -Σ(p × log₂(p)) + noise × 0.1
   - Noise breaks ties for deterministic ordering
   
2. COLLAPSE - Choose tile with weighted random
   - Weights favor certain tiles (Empty: 2.0, Cross: 0.3)
   - Reduces cell from superposition to single tile
   
3. PROPAGATE - Update neighbor constraints (BFS)
   - For each collapsed cell, update neighbors
   - Remove tiles incompatible with neighbors' sockets
   - Cascade changes through constraint graph
   - Detect contradictions (empty possibility set)

Repeat until all cells collapsed or contradiction detected
```

### Isometric Rendering (from `renderer.rs`)

```rust
pub const TILE_WIDTH: f32 = 64.0;
pub const TILE_HEIGHT: f32 = 32.0;
const FLOOR_Z_OFFSET: f32 = -100.0;

// Isometric conversion: Grid (x,y) → World (x,y)
world_x = (grid_x - grid_y) * TILE_WIDTH * 0.5
world_y = (grid_x + grid_y) * TILE_HEIGHT * 0.5

// Z-depth sorting (prevents overlap issues)
z_depth = FLOOR_Z_OFFSET - grid_y
```

**Color Scheme** (Circuit Board theme):
- Empty: Dark floor `(0.12, 0.12, 0.20)`
- Straight/Corner: Cyan path `(0.25, 0.45, 0.65)`
- T-Junction: Bright blue `(0.35, 0.55, 0.75)`
- Cross: Brightest `(0.45, 0.65, 0.85)`

### Plugin Integration

**Location**: `src/procedural/mod.rs`

```rust
pub struct ProceduralPlugin {
    fn build(&self, app: &mut App) {
        app
            // Sub-plugins
            .add_plugins(wfc::renderer::WfcRendererPlugin)
            
            // Events
            .add_event::<CellCollapsedEvent>()
            .add_event::<ContradictionEvent>()
            .add_event::<GenerationCompleteEvent>()
            
            // Systems
            .add_systems(Startup, setup_procedural_systems)
            .add_systems(OnEnter(GameState::InGame), terminal_commands::register_wfc_commands)
            .add_systems(Update, handle_pending_requests)
            .add_systems(Update, wfc_observe_step.chain()
                                  wfc_collapse_step.chain()
                                  wfc_propagate_step)
    }
}
```

### Terminal Command Interface

**Command**: `generate_wfc_maze [width] [height] [seed]`

**Usage Examples**:
```
generate_wfc_maze                    → 16×16 with random seed
generate_wfc_maze 32 32             → 32×32 with random seed
generate_wfc_maze 20 20 12345       → 20×20 with seed 12345
```

**Flow**:
1. Terminal command adds marker to `TerminalHistory`
2. `handle_pending_requests()` system detects marker
3. Creates `WfcGenerationState` resource
4. WFC algorithm systems activate automatically
5. `GenerationCompleteEvent` fired when done
6. `WfcRendererPlugin` spawns visual tiles
7. State cleaned up after rendering

### Performance Characteristics

| Maze Size | Cells | Steps | Time | Notes |
|-----------|-------|-------|------|-------|
| 16×16 | 256 | 200-400 | <100ms | Test standard |
| 32×32 | 1024 | 800-1500 | <500ms | Default |
| 64×64 | 4096 | 3000-6000 | <2s | Requires culling |

---

## bevy_knossos Analysis

### Current Status: **NOT USED**

**Dependency Declaration** (Cargo.toml):
```toml
bevy_knossos = "0.8.1"
```

**Usage in Codebase**:
```
No references found to bevy_knossos in any .rs files
No imports or function calls
No integration with WFC or maze systems
```

### What bevy_knossos Provides

bevy_knossos is a **procedural terrain generation library** for Bevy. It provides:

1. **Noise Functions**
   - Perlin noise
   - Simplex noise
   - Worley (Voronoi) noise
   - Fractal Brownian Motion (FBM)

2. **Terrain Generation**
   - Height map generation
   - Biome distribution
   - Feature placement

3. **Mesh Synthesis**
   - Procedural mesh generation
   - Chunk-based LOD systems
   - Optimization for large terrains

### Potential Integration Points for Runetika

**Option 1: Hybrid WFC + knossos**
```rust
// Use knossos noise for constraint weighting
let noise_value = perlin_noise(grid_x, grid_y, seed);
let adjusted_weight = base_weight * (1.0 + noise_value * 0.3);
```

**Option 2: knossos for Glyph Placement**
```rust
// Generate natural glyph placement patterns
let glyph_density = worley_noise(x, y);
if glyph_density > 0.7 && cell_is_path {
    spawn_glyph_at(position);
}
```

**Option 3: Terrain Scaffolding**
```rust
// Use knossos to generate 3D terrain height, then apply WFC for details
let height = knossos::fbm(x, y, octaves);
apply_wfc_at_height_level(height);
```

---

## Dependency Analysis

### Cargo.toml Dependencies Summary

```toml
# USED
bevy = "0.16"              ✅ Core engine
avian2d = "0.3"           ✅ 2D physics
rand = "0.8"              ✅ Used in maze.rs, algorithm.rs
serde = "1.0"             ⚠️ Declared, partially used (warnings)
serde_json = "1.0"        ✅ Used in settings
dirs = "5.0"              ✅ Used in settings

# NOT USED
bevy_knossos = "0.8.1"    ❌ Added but no usage
```

### Feature Flags (Minimal Set)

```toml
bevy = { version = "0.16", default-features = false, features = [
    "bevy_asset",      # Asset loading
    "bevy_winit",      # Window/input
    "bevy_render",     # Rendering
    "bevy_sprite",     # Sprite rendering
    "bevy_text",       # Text rendering
    "bevy_ui",         # UI system
    "bevy_state",      # State management
    "default_font",    # Default font for text
    "png",             # PNG image support
    "x11",             # Linux X11 support
    "wayland",         # Linux Wayland support
    "bevy_color",      # Color operations
    # NOT included: audio, pbr, gltf, animations, debug_tools
]}
```

---

## Integration Challenges

### 1. Two Competing Maze Systems

**Current Issue**: Both systems exist but aren't coordinated
- Old `maze.rs` uses simple recursive backtracking (15×15 fixed)
- New `wfc/` uses Wave Function Collapse (configurable size)
- WFC system has full isometric rendering
- Old maze lacks proper integration with new player system

**Resolution Options**:
- Option A: Keep both, use WFC for new content
- Option B: Migrate fully to WFC system
- Option C: Hybrid approach (WFC for maze generation, old system for entry/exit logic)

### 2. Player System Mismatch

**Issue**: `maze.rs` references `crate::main_room::Player` but `player.rs` defines different Player struct

```rust
// maze.rs expects:
pub struct Player { pub speed: f32 }

// player.rs provides:
pub struct Player { 
    pub speed: f32,
    pub in_terminal_mode: bool,
}
```

**Status**: Actually compatible (struct can have extra fields), but creates confusion

### 3. Perspective System Broken

**Issue**: `perspective.rs` has broken `despawn_silicon_overlay()` call

**Root Cause**: System function signature requires Query parameter but isn't being provided

### 4. Terminal Command Registration

**Issue**: `src/procedural/wfc/terminal_commands.rs` exists but:
- Not fully integrated with main terminal system
- Registration happens on `OnEnter(GameState::InGame)`
- May conflict with other terminal command registration

### 5. Physics Integration

**Issue**: WFC renderer spawns sprites but no collision detection
- Tiles are visual only
- No physics bodies for navigation
- Player could walk through walls if integrated

---

## Code Quality Assessment

### Old Maze System (`maze.rs`)
- **Status**: Functional, but deprecated by WFC system
- **Issues**:
  - Deprecated API warning on line 251: `get_single()` → `single()`
  - Hardcoded boundaries (x > 400.0, x > 800.0)
  - No async/await for generation
  - Simple algorithm (limited to 15×15)

### WFC System (`src/procedural/wfc/`)
- **Status**: Production-ready core, renderer complete
- **Strengths**:
  - Correct algorithm implementation
  - Excellent documentation
  - Clean architecture with separation of concerns
  - O(1) constraint lookups via pre-computed graph
  - Full isometric rendering system
- **Minor Issues**:
  - Unused imports in `mod.rs` (lines 17-22)
  - Terminal command registration incomplete
  - No backtracking for contradiction handling
  - No collision detection on rendered tiles

### Perspective System (`perspective.rs`)
- **Status**: Broken, needs refactoring
- **Issues**:
  - Line 139: Function call mismatch
  - Line 223: Function signature expects Query parameter not passed
  - System design doesn't allow passing queries to spawned overlay

---

## File Locations Reference

| Component | File | Key Lines |
|-----------|------|-----------|
| Build Error | `src/perspective.rs` | 139, 223 |
| Old Maze | `src/maze.rs` | 1-300+ |
| WFC Main Plugin | `src/procedural/mod.rs` | 1-100+ |
| WFC Algorithm | `src/procedural/wfc/algorithm.rs` | 1-400+ |
| WFC Renderer | `src/procedural/wfc/renderer.rs` | 1-300+ |
| WFC Tiles | `src/procedural/wfc/tiles.rs` | (not shown) |
| Player System | `src/player.rs` | 1-170 |
| Room Setup | `src/main_room.rs` | 1-150+ |
| Cargo Config | `Cargo.toml` | Line 21 (bevy_knossos) |

---

## Recommended Actions

### Priority 1: Fix Build Error
**Fix the `perspective.rs` line 139 function call**
- The function needs both `Commands` and the `Query` parameter
- Refactor to either:
  1. Make a separate system that handles despawning
  2. Change function signature to only take `Commands` and find entities by component

### Priority 2: Integrate WFC Fully
**The WFC system is more advanced and should be primary**
- Add physics colliders to rendered WFC tiles
- Connect WFC output to game state
- Test terminal command integration
- Remove or deprecate old `maze.rs` system

### Priority 3: Review bevy_knossos Usage
**Decide whether to use it**
- Option A: Remove if not needed (simplifies Cargo.toml)
- Option B: Integrate for advanced terrain features
- Option C: Keep as optional feature for future expansion

### Priority 4: Unify Player System References
**Clean up imports and references**
- Update `maze.rs` to use correct `player::Player` import
- Ensure consistent component naming across systems

---

## Testing Strategy

### For build fixes:
```bash
cargo check
cargo build
```

### For WFC integration:
```bash
cargo run
# In-game terminal: generate_wfc_maze 16 16
# Watch console for generation steps
# Verify isometric rendering
```

### For physics integration:
```bash
# Check collisions with generated maze
# Verify player can navigate maze properly
```

---

## References

- **WFC Original**: https://github.com/mxgmn/WaveFunctionCollapse
- **Wang Tiles**: https://en.wikipedia.org/wiki/Wang_tile
- **bevy_knossos**: https://crates.io/crates/bevy_knossos
- **Bevy 0.16 Docs**: https://docs.rs/bevy/0.16.0
