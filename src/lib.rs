/// Runetika Library
/// Provides both desktop and Android support

// Android module (only compiled for Android targets)
#[cfg(target_os = "android")]
pub mod android;

// iOS module (only compiled for iOS targets)
#[cfg(target_os = "ios")]
pub mod ios;

// Re-export all game modules
pub mod game_state;
pub mod menu;
pub mod terminal;
pub mod settings;
pub mod credits;
pub mod performance;
pub mod main_room;
pub mod maze;
pub mod player;
pub mod perspective;
pub mod puzzle;
pub mod silicon_mind;
pub mod spaceship;
pub mod spaceship_2d;
pub mod terminal_interface;
pub mod terminal_commands;

// Re-export GameState for convenience
pub use game_state::{GameState, GameStatePlugin};

// Re-export for convenience
pub use bevy;
pub use avian2d;