use bevy::prelude::*;

#[derive(Component)]
pub struct Terminal;

#[derive(Component)]
pub struct TerminalDisplay;

#[derive(Component)]
pub struct TerminalInputLine;

#[derive(Component)]
pub struct TerminalOutputLine {
    #[allow(dead_code)]
    pub index: usize,
}

#[derive(Component)]
pub struct TerminalCursor;

#[derive(Component)]
#[allow(dead_code)]
pub struct TerminalScrollbar;

#[derive(Component)]
pub struct TerminalBackground;

#[derive(Component)]
pub struct TerminalPrompt;