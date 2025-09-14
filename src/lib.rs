/// Runetika Library Entry Point
/// 
/// This file serves as the library entry point for FFI and external integrations.
/// It's primarily used for iOS builds where Runetika is compiled as a static library.

// Re-export all game modules
pub mod menu;
pub mod settings;
pub mod credits;
pub mod silicon_mind;
pub mod terminal_interface;
pub mod terminal_commands;
pub mod perspective;
pub mod player;
pub mod spaceship;
pub mod puzzle;
pub mod arc_engine;
pub mod papilio;

// Terminal module for compatibility
pub mod terminal {
    pub use crate::terminal_interface::*;
    
    // Re-export the InteractableTerminal from perspective module
    pub use crate::perspective::InteractableTerminal;
}

// iOS FFI bridge - only compile for iOS targets
#[cfg(any(target_os = "ios", feature = "ios-ffi"))]
pub mod ios_ffi;

// Re-export game state for FFI access
pub use crate::game_state::GameState;

// Game state module
pub mod game_state {
    use bevy::prelude::*;
    
    /// Core game state management
    #[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Hash, States)]
    pub enum GameState {
        #[default]
        MainMenu,
        InGame,
        Settings,
        Credits,
        Terminal,
    }
}