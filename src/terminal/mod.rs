//! Terminal Module - The Heart of Gameplay
//! 
//! # Conceptual Overview
//! The terminal is more than just a command interface - it's a narrative device,
//! a puzzle-solving tool, and the primary way players interact with the game world.
//! Think of it as a conversation with the game's AI, where commands shape the story.
//!
//! # Module Structure
//! - `components`: Data structures (ECS components) for terminal elements
//! - `systems`: Game logic that updates the terminal each frame
//! - `commands`: Available commands and their implementations
//! - `ui`: Visual layout and styling
//! - `starfield`: Background animation for atmosphere

pub mod components;
pub mod systems;
pub mod commands;
pub mod ui;
pub mod starfield;

// Re-export commonly used items
pub use crate::perspective::InteractableTerminal;

use bevy::prelude::*;
use self::systems::*;
use self::ui::*;
use self::commands::register_builtin_commands;
use self::starfield::*;
use crate::game_state::GameState;

/// Main terminal plugin - Integrates all terminal functionality into Bevy
/// 
/// # Plugin Pattern
/// Bevy uses plugins to modularize functionality. This plugin adds all the
/// systems, resources, and components needed for the terminal to work.
/// 
/// # System Ordering
/// Systems are chained (.chain()) to ensure they run in the correct order.
/// This prevents race conditions and ensures smooth updates.
pub struct TerminalPlugin;

impl Plugin for TerminalPlugin {
    fn build(&self, app: &mut App) {
        app
            .init_resource::<TerminalState>()
            .init_resource::<TerminalHistory>()
            .init_resource::<CommandRegistry>()
            .add_systems(OnEnter(GameState::InGame), (
                setup_starfield,
                setup_terminal,
                register_builtin_commands,
                initialize_terminal,
                create_scanline_effect,
            ).chain())
            .add_systems(OnExit(GameState::InGame), cleanup_terminal)
            .add_systems(Update, (
                handle_terminal_input,
                update_terminal_display,
                process_terminal_commands,
                handle_terminal_scrolling,
                animate_cursor,
                animate_stars,
                animate_terminal_glow,
            ).chain().run_if(in_state(GameState::InGame)));
    }
}

/// Terminal state - Tracks all mutable terminal data
/// 
/// # State Management Philosophy  
/// This resource acts as the single source of truth for terminal state.
/// It's global (Resource) rather than per-entity because there's only one terminal.
/// 
/// # Fields Explained
/// - `input_buffer`: Current text being typed (before pressing Enter)
/// - `cursor_position`: Where the text cursor is (for editing)
/// - `is_active`: Whether terminal accepts input (vs being hidden)
/// - `scroll_offset`: How far up the user has scrolled in history
#[derive(Resource, Default)]
pub struct TerminalState {
    pub input_buffer: String,
    pub cursor_position: usize,
    pub is_active: bool,
    pub scroll_offset: usize,
}

/// Command history - Stores past commands and outputs
/// 
/// # Memory Design
/// Stores both the display lines and command history separately.
/// Limited to max_lines to prevent unbounded memory growth.
/// 
/// # User Experience
/// - `lines`: All terminal output for display
/// - `command_history`: Just the commands for up/down navigation
/// - `history_index`: Current position when navigating history
#[derive(Resource)]
pub struct TerminalHistory {
    pub lines: Vec<TerminalLine>,
    pub command_history: Vec<String>,
    pub history_index: Option<usize>,
    pub max_lines: usize,
}

/// Single line of terminal output with metadata
/// 
/// # Data Structure
/// Each line knows its type (input/output/error) for styling,
/// and when it was created (timestamp) for animations or filtering.
#[derive(Clone)]
pub struct TerminalLine {
    pub text: String,
    pub line_type: LineType,
    pub timestamp: f64,
}

/// Categories of terminal output for different visual styling
/// 
/// # Visual Semantics
/// Each type gets different colors/formatting:
/// - Input: User commands (white/bright)
/// - Output: Normal responses (cyan)
/// - Error: Problems (red)
/// - System: Game messages (yellow)
/// - Success: Achievements (green)
#[derive(Clone, Debug)]
pub enum LineType {
    Input,
    Output,
    Error,
    System,
    Success,
}

impl Default for TerminalHistory {
    fn default() -> Self {
        Self {
            lines: Vec::new(),
            command_history: Vec::new(),
            history_index: None,
            max_lines: 1000,
        }
    }
}

/// Command registry - Dynamic command management system
/// 
/// # Design Pattern: Command Pattern + Registry
/// Commands are registered at runtime, allowing modular addition.
/// Uses trait objects (Box<dyn Command>) for polymorphism.
/// 
/// # Abstract View
/// This is a function dispatch table - maps strings to executable code.
/// It's how we achieve late binding in a statically typed language.
#[derive(Resource, Default)]
pub struct CommandRegistry {
    pub commands: std::collections::HashMap<String, Box<dyn Command>>,
}

/// Command trait - Interface all terminal commands must implement
/// 
/// # Trait Design
/// - `Send + Sync`: Required for Bevy's parallel systems
/// - `execute`: The actual command logic
/// - `help`: Documentation for users
/// - `autocomplete`: Optional smart suggestions
/// 
/// # Extending the Game
/// New commands just implement this trait and register themselves.
pub trait Command: Send + Sync {
    fn execute(&self, args: Vec<String>, terminal: &mut TerminalHistory) -> CommandResult;
    fn help(&self) -> String;
    fn autocomplete(&self, _partial: &str) -> Vec<String> {
        Vec::new()
    }
}

/// Result of command execution
/// 
/// # Result Semantics
/// - Success: Command worked, show this message
/// - Error: Command failed, show error message
/// - Continue: Command handled internally, no message
pub enum CommandResult {
    Success(String),
    Error(String),
    Continue,
}