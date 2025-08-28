# Runetika Project Structure

## Overview
Runetika is a top-down RPG prototype built with Bevy and Avian2D, focusing on love, hope, and human emotion through mystical realism and artistic style.

## Directory Structure

```
OurRunetika/
├── assets/                 # Game assets (fonts, images, audio)
│   └── fonts/            # Typography assets
├── src/                   # Source code
│   ├── credits/          # Credits and attribution systems
│   │   ├── mod.rs        # Module definition
│   │   ├── systems.rs    # ECS systems for credits
│   │   └── ui.rs         # User interface for credits
│   ├── game_state.rs     # Game state management
│   ├── main.rs           # Main application entry point
│   ├── main_documented.rs # Documented version of main
│   ├── menu/             # Menu system components
│   │   ├── components.rs # Menu UI components
│   │   ├── mod.rs        # Menu module definition
│   │   ├── systems.rs    # Menu ECS systems
│   │   ├── ui_old.rs     # Legacy menu UI (deprecated)
│   │   └── ui.rs         # Current menu UI implementation
│   ├── performance/      # Performance monitoring and optimization
│   │   └── mod.rs        # Performance module
│   ├── settings/         # Game settings and configuration
│   │   ├── components.rs # Settings UI components
│   │   └── mod.rs        # Settings module
│   └── terminal/         # Terminal/console system
│       ├── commands.rs   # Terminal command definitions
│       ├── components.rs # Terminal UI components
│       ├── mod.rs        # Terminal module
│       ├── starfield.rs  # Starfield background effect
│       ├── systems.rs    # Terminal ECS systems
│       └── ui.rs         # Terminal user interface
├── tools/                 # Development and build tools
│   ├── build_docs.sh     # Documentation builder
│   ├── debug_analysis.sh # Code analysis and debugging
│   └── update-deps.sh    # Dependency update script
├── target/                # Build artifacts (generated)
├── Cargo.toml            # Rust project configuration
├── Cargo.lock            # Dependency lock file
├── Cargo_optimized.toml  # Optimized build configuration
├── rust-toolchain.toml   # Rust toolchain specification
├── README.md             # Project overview and setup
├── WARP.md               # Project documentation
├── LICENSE               # Project license
├── renovate.json         # Dependency update configuration
└── RESEARCH_AND_NEXT_STEPS.md # Research and development roadmap
```

## Architecture Overview

### ECS (Entity-Component-System) Architecture
The project uses Bevy's ECS architecture for efficient game development:

- **Entities**: Game objects (player, NPCs, items, etc.)
- **Components**: Data attached to entities (position, health, inventory, etc.)
- **Systems**: Logic that operates on entities with specific components

### Module Organization
Each major feature is organized into its own module with:
- `mod.rs`: Module definition and public interface
- `systems.rs`: ECS systems for the module
- `ui.rs`: User interface components
- `components.rs`: Reusable UI components

### Key Systems
1. **Game State Management**: Handles transitions between game states
2. **Menu System**: Provides navigation and game options
3. **Terminal System**: Console interface for debugging and commands
4. **Performance Monitoring**: Tracks and optimizes game performance
5. **Settings Management**: Handles user preferences and configuration

## Dependencies

### Core Dependencies
- **Bevy 0.16**: Game engine with ECS architecture
- **Avian2D 0.2**: Experimental 2D physics engine
- **Rand 0.8**: Random number generation

### Development Dependencies
- **rust-toolchain.toml**: Specifies Rust version and components
- **renovate.json**: Automates dependency updates

## Build Configuration

### Cargo.toml
- Main project configuration
- Dependency specifications
- Build targets and features

### Cargo_optimized.toml
- Optimized build configuration for production
- Performance-focused compiler flags
- Release build settings

## Asset Management

### Fonts
- Located in `assets/fonts/`
- Typography for UI elements
- Consistent visual identity

### Future Asset Categories
- **Images**: Sprites, textures, backgrounds
- **Audio**: Music, sound effects, ambient sounds
- **Data**: Game configuration, level data, dialogue

## Development Workflow

### Tools
- **build_docs.sh**: Generates comprehensive documentation
- **debug_analysis.sh**: Analyzes code quality and performance
- **update-deps.sh**: Manages dependency updates

### Documentation
- **README.md**: Quick start and overview
- **WARP.md**: Detailed project documentation
- **RESEARCH_AND_NEXT_STEPS.md**: Development roadmap
- **docs/**: Generated documentation

### Quality Assurance
- Automated post-commit hooks
- Comprehensive debugging and analysis
- Continuous documentation updates

## Future Considerations

### Scalability
- Modular architecture supports feature expansion
- ECS pattern enables efficient performance scaling
- Asset pipeline designed for content growth

### Maintainability
- Clear separation of concerns
- Consistent coding patterns
- Comprehensive documentation

### Performance
- Built-in performance monitoring
- Optimized build configurations
- Efficient asset loading strategies

---

*Generated automatically by build_docs.sh*

