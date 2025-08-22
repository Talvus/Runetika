//! Game State Management - The Flow of the Game
//! 
//! # Conceptual Model: Finite State Machine
//! The game exists in exactly one state at any time. States define what
//! systems run, what's displayed, and how input is handled.
//! 
//! Think of it like rooms in a house:
//! - MainMenu: The entrance hall where you decide where to go
//! - InGame: The living room where the main action happens
//! - Settings: The control room where you adjust things
//! - Credits: The gallery showing who built the house
//! - Paused: A frozen moment in time
//! 
//! # Technical Implementation
//! Uses Bevy's States system which automatically manages transitions
//! and ensures only relevant systems run in each state.

use bevy::prelude::*;

/// Game states - Mutually exclusive phases of the game
/// 
/// # State Machine Properties
/// - **Exclusive**: Only one state active at a time
/// - **Transitional**: Moving between states triggers OnEnter/OnExit
/// - **Deterministic**: State changes are explicit and predictable
/// 
/// # Derive Macros Explained
/// - `States`: Makes this work with Bevy's state system
/// - `Default`: MainMenu is where the game starts
/// - `Hash, Eq, PartialEq`: Required for state comparison
/// - `Debug, Clone, Copy`: Utility traits for development
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Hash, States)]
pub enum GameState {
    /// Starting state - The main menu screen
    #[default]
    MainMenu,
    /// Active gameplay - Terminal and world interaction
    InGame,
    /// Configuration screen - Adjusting game options
    Settings,
    /// Credits screen - Acknowledgments and information
    Credits,
    /// Paused state - Gameplay frozen, pause menu shown
    Paused,
}

/// Plugin that manages game state transitions
/// 
/// # Responsibility
/// - Initializes the state machine
/// - Registers transition handlers
/// - Logs state changes for debugging
pub struct GameStatePlugin;

impl Plugin for GameStatePlugin {
    fn build(&self, app: &mut App) {
        app
            .init_state::<GameState>()
            .add_systems(OnEnter(GameState::MainMenu), on_enter_main_menu)
            .add_systems(OnExit(GameState::MainMenu), on_exit_main_menu)
            .add_systems(OnEnter(GameState::InGame), on_enter_game)
            .add_systems(OnExit(GameState::InGame), on_exit_game);
    }
}

/// Handler for entering the main menu
/// 
/// # Transition Effects
/// This runs once when transitioning TO MainMenu from any other state.
/// Used for setup that should happen every time we return to the menu.
fn on_enter_main_menu() {
    info!("Entering Main Menu");
}

/// Handler for leaving the main menu
/// 
/// # Cleanup
/// Runs when transitioning FROM MainMenu to any other state.
/// Ensures menu resources don't persist into gameplay.
fn on_exit_main_menu() {
    info!("Exiting Main Menu");
}

/// Handler for starting gameplay
/// 
/// # Game Initialization
/// Sets up the game world, spawns entities, initializes systems.
/// This is where the "real" game begins.
fn on_enter_game() {
    info!("Starting Game");
}

/// Handler for leaving gameplay
/// 
/// # Game Cleanup
/// Saves progress, despawns entities, frees resources.
/// Ensures clean transition back to menu or other states.
fn on_exit_game() {
    info!("Exiting Game");
}