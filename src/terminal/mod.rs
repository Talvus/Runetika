pub mod components;
pub mod systems;
pub mod commands;
pub mod ui;
pub mod starfield;

use bevy::prelude::*;
use self::systems::*;
use self::ui::*;
use self::commands::register_builtin_commands;
use self::starfield::*;

pub struct TerminalPlugin;

impl Plugin for TerminalPlugin {
    fn build(&self, app: &mut App) {
        app
            .init_resource::<TerminalState>()
            .init_resource::<TerminalHistory>()
            .init_resource::<CommandRegistry>()
            .add_systems(Startup, (
                setup_starfield,
                setup_terminal,
                register_builtin_commands,
                initialize_terminal,
                create_scanline_effect,
            ).chain())
            .add_systems(Update, (
                handle_terminal_input,
                update_terminal_display,
                process_terminal_commands,
                handle_terminal_scrolling,
                animate_cursor,
                animate_stars,
                animate_terminal_glow,
            ).chain());
    }
}

#[derive(Resource, Default)]
pub struct TerminalState {
    pub input_buffer: String,
    pub cursor_position: usize,
    pub is_active: bool,
    pub scroll_offset: usize,
}

#[derive(Resource)]
pub struct TerminalHistory {
    pub lines: Vec<TerminalLine>,
    pub command_history: Vec<String>,
    pub history_index: Option<usize>,
    pub max_lines: usize,
}

#[derive(Clone)]
pub struct TerminalLine {
    pub text: String,
    pub line_type: LineType,
    pub timestamp: f64,
}

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

#[derive(Resource, Default)]
pub struct CommandRegistry {
    pub commands: std::collections::HashMap<String, Box<dyn Command>>,
}

pub trait Command: Send + Sync {
    fn execute(&self, args: Vec<String>, terminal: &mut TerminalHistory) -> CommandResult;
    fn help(&self) -> String;
    fn autocomplete(&self, _partial: &str) -> Vec<String> {
        Vec::new()
    }
}

pub enum CommandResult {
    Success(String),
    Error(String),
    Continue,
}