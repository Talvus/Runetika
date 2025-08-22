# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Essential Commands

### Building and Running
```bash
# Standard development build (fast compilation, optimized dependencies)
cargo build

# Release build (full optimization)
cargo build --release

# Run the game
cargo run

# Run in release mode
cargo run --release
```

### Development Tools
```bash
# Code quality and debugging analysis
./tools/debug_analysis.sh

# Build comprehensive documentation
./tools/build_docs.sh

# Update dependencies
./tools/update-deps.sh

# Lint with strict warnings
cargo clippy -- -D warnings

# Check formatting
cargo fmt -- --check
```

### Cargo Aliases (from .cargo/config.toml)
```bash
# Security audit
cargo audit

# Format and lint
cargo lint          # equivalent to: cargo clippy -- -D warnings
cargo fmt-check     # equivalent to: cargo fmt -- --check

# Platform builds
cargo build-all     # builds for macOS Intel, Apple Silicon, and WASM
```

### Testing
Currently no test suite exists - this is a prototype focusing on game development and documentation.

## Architecture Overview

### Core Design Philosophy
Runetika follows a **modular ECS architecture** where each major game system is self-contained but communicates through Bevy's ECS. The game is about "love, hope, and human emotion" through mystical realism, centered on a fallen silicon-based civilization.

### State Machine Flow
```
MainMenu → InGame → [Settings/Credits] → MainMenu
     ↓       ↓           ↑
   Exit   Terminal    Back/ESC
```

The `GameState` enum drives the entire application flow. Each state activates different plugins and systems.

### Module Architecture

**Terminal System** (`src/terminal/`) - **Primary Gameplay Interface**
- This is where "most of the gameplay will occur" 
- Command-line interface in a space theme
- Plugin pattern: `TerminalPlugin` manages all terminal functionality
- Key components: input handling, command registry, visual rendering
- Uses a command pattern with trait objects for extensible commands

**Menu System** (`src/menu/`)
- State-driven navigation with smooth transitions
- Enhanced UI with starfield backgrounds, particle effects
- Keyboard and mouse navigation support
- Plugin: `MainMenuPlugin`

**Settings System** (`src/settings/`)
- Complete configuration management with persistence
- Platform-specific optimizations (especially Apple Silicon)
- Serializable settings stored in platform-appropriate directories
- Categories: Graphics, Audio, Controls, Gameplay

**Performance System** (`src/performance/`)
- Real-time performance monitoring and auto-optimization
- Platform-specific detection (macOS hardware capabilities)
- Quality adjustment based on frame rate performance

**Credits System** (`src/credits/`)
- Scrolling credits with fade animations
- Team acknowledgments and technology credits

### Key Implementation Patterns

**Plugin Architecture**: Each major system implements Bevy's `Plugin` trait
```rust
impl Plugin for SystemPlugin {
    fn build(&self, app: &mut App) {
        app.add_systems(OnEnter(GameState::System), setup_system)
           .add_systems(Update, update_systems.run_if(in_state(GameState::System)));
    }
}
```

**State-Driven Systems**: Systems run conditionally based on `GameState`
- Use `.run_if(in_state(GameState::Target))` for state-specific systems
- `OnEnter`/`OnExit` for setup and cleanup

**Resource-Based Configuration**: Global state via Bevy Resources
- Settings, performance metrics, menu state are all Resources
- Accessed via `Res<T>` and `ResMut<T>` in systems

## Code Style and Documentation

### Documentation Philosophy
Code is documented for **both abstract and concrete thinkers**:
- Abstract concepts explain theoretical models and design patterns
- Concrete explanations provide practical implementation details
- Every public function has comprehensive `///` documentation

### Accessibility Approach
The user is a "strongly abstract thinker" but others will read this code, so:
- Bridge abstract concepts with concrete implementations
- Explain both "what" and "why" in documentation
- Use mathematical/theoretical models where relevant

## Build Configuration

### Development Optimizations
- Dependencies are optimized even in debug mode (`opt-level = 3`)
- Your code compiles with minimal optimization (`opt-level = 1`)
- Platform-specific linker optimizations (lld, mold)

### Platform-Specific Features
- **Apple Silicon**: `target-cpu=apple-m1` optimization
- **macOS**: Split debug info for better debugging
- **Linux**: mold/lld linker for faster linking
- **WASM**: Configured for web deployment

## Key Dependencies

- **bevy = "0.16"**: Game engine (ECS, rendering, input, audio)
- **avian2d = "0.2"**: 2D physics (currently minimal usage)
- **rand = "0.8"**: Random generation for procedural content
- **serde + serde_json**: Settings serialization
- **dirs**: Platform-appropriate directory detection

## Development Workflow

### Automated System
This repository has **post-commit automation** that runs after every commit:
1. Builds documentation
2. Updates research roadmap
3. Runs debugging analysis  
4. Creates commit summaries

### Manual Quality Checks
```bash
# Run before committing
cargo clippy -- -D warnings
cargo build --release
./tools/debug_analysis.sh
```

## Important Notes

### Security
- No unsafe code in source files (recently eliminated from performance module)
- No hardcoded secrets or credentials
- File operations are sandboxed to appropriate directories
- Thread-safe atomic operations instead of unsafe statics

### Performance Considerations
- Built-in performance monitoring with auto-quality adjustment
- Platform detection for optimal settings
- Efficient ECS queries and system organization
- Asset optimization for different platforms

### Future Development Areas
The game concept involves:
- Glyph puzzles and pattern recognition (ARC-style puzzles)
- Terminal-driven exploration and interaction
- Silicon civilization mystery and technology themes
- Mystical realism artistic direction