/// Runetika Library
/// Provides both desktop and Android support

// Android module (only compiled for Android targets)
#[cfg(target_os = "android")]
pub mod android;

// Re-export core game modules
pub mod menu;
pub mod terminal;
pub mod settings;
pub mod credits;
pub mod performance;
pub mod main_room;

// Core game state
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GameState {
    MainMenu,
    InGame,
    Settings,
    Credits,
}

// Re-export for convenience
pub use bevy;
pub use avian2d;