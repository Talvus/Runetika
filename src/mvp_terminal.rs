use bevy::prelude::*;
use crate::arc_engine::{PuzzleState, Grid, Cell, Color as ARCColor, puzzles};

pub struct MVPTerminalPlugin;

impl Plugin for MVPTerminalPlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(MVPTerminalState::default())
            .add_systems(Startup, setup_mvp_terminal)
            .add_systems(Update, (
                handle_terminal_input,
                update_terminal_display,
                process_puzzle_commands,
            ));
    }
}

#[derive(Resource)]
pub struct MVPTerminalState {
    pub input_buffer: String,
    pub output_lines: Vec<String>,
    pub command_history: Vec<String>,
    pub silicon_voice: bool,
}

impl Default for MVPTerminalState {
    fn default() -> Self {
        Self {
            input_buffer: String::new(),
            output_lines: vec![
                "╔════════════════════════════════════════════╗".to_string(),
                "║         RUNETIKA - SILICON MIND           ║".to_string(),
                "║            Terminal Interface              ║".to_string(),
                "╚════════════════════════════════════════════╝".to_string(),
                "".to_string(),
                "You awaken in the digital void...".to_string(),
                "The Silicon Mind whispers: \"Can you see the patterns?\"".to_string(),
                "".to_string(),
                "Type 'help' for commands or 'start' to begin.".to_string(),
                "".to_string(),
            ],
            command_history: Vec::new(),
            silicon_voice: true,
        }
    }
}

fn setup_mvp_terminal(
    mut commands: Commands,
) {
    // Camera
    commands.spawn(Camera2dBundle::default());
    
    // Terminal background
    commands.spawn(SpriteBundle {
        sprite: Sprite {
            color: Color::srgb(0.05, 0.05, 0.1),
            custom_size: Some(Vec2::new(1280.0, 800.0)),
            ..default()
        },
        ..default()
    });
    
    // Terminal text
    commands.spawn((
        Text2dBundle {
            text: Text::from_section(
                "",
                TextStyle {
                    font_size: 16.0,
                    color: Color::srgb(0.0, 1.0, 0.3),
                    ..default()
                },
            ),
            transform: Transform::from_xyz(-600.0, 350.0, 1.0),
            ..default()
        },
        TerminalDisplay,
    ));
}

#[derive(Component)]
struct TerminalDisplay;

fn handle_terminal_input(
    mut terminal: ResMut<MVPTerminalState>,
    keyboard: Res<ButtonInput<KeyCode>>,
    mut char_events: EventReader<ReceivedCharacter>,
) {
    // Handle character input
    for event in char_events.read() {
        if event.char != '\r' && event.char != '\n' {
            terminal.input_buffer.push(event.char);
        }
    }
    
    // Handle special keys
    if keyboard.just_pressed(KeyCode::Enter) {
        let command = terminal.input_buffer.clone();
        terminal.command_history.push(command.clone());
        terminal.output_lines.push(format!("> {}", command));
        
        // Process command
        let response = process_command(&command);
        for line in response.lines() {
            terminal.output_lines.push(line.to_string());
        }
        
        terminal.input_buffer.clear();
    }
    
    if keyboard.just_pressed(KeyCode::Backspace) && !terminal.input_buffer.is_empty() {
        terminal.input_buffer.pop();
    }
}

fn update_terminal_display(
    terminal: Res<MVPTerminalState>,
    mut query: Query<&mut Text, With<TerminalDisplay>>,
) {
    if let Ok(mut text) = query.get_single_mut() {
        let mut display = String::new();
        
        // Show last 25 lines
        let start = terminal.output_lines.len().saturating_sub(25);
        for line in &terminal.output_lines[start..] {
            display.push_str(line);
            display.push('\n');
        }
        
        // Add current input
        display.push_str(&format!("> {}_", terminal.input_buffer));
        
        text.sections[0].value = display;
    }
}

fn process_command(command: &str) -> String {
    let parts: Vec<&str> = command.split_whitespace().collect();
    
    match parts.first().map(|s| *s) {
        Some("help") => {
            "Commands:\n\
             start    - Begin the puzzle sequence\n\
             puzzle   - Show current puzzle\n\
             solve    - Submit your solution\n\
             hint     - Ask the Silicon Mind for guidance\n\
             clear    - Clear the terminal\n\
             about    - Learn about Runetika"
        }
        Some("start") => {
            "Initializing puzzle sequence...\n\
             The Silicon Mind awakens: \"Welcome, pattern seeker.\"\n\
             \n\
             Use 'puzzle' to see your first challenge."
        }
        Some("clear") => {
            "\x1B[2J\x1B[H"
        }
        Some("about") => {
            "RUNETIKA - A game of patterns, consciousness, and connection.\n\
             You are interfacing with the Silicon Mind, a remnant of a fallen\n\
             digital civilization. Through puzzles and glyphs, you will learn\n\
             to think as they once did."
        }
        _ => {
            "Unknown command. Type 'help' for available commands."
        }
    }.to_string()
}

fn process_puzzle_commands(
    mut terminal: ResMut<MVPTerminalState>,
    mut puzzle_state: ResMut<PuzzleState>,
    keyboard: Res<ButtonInput<KeyCode>>,
) {
    // Initialize puzzles if needed
    if puzzle_state.current_puzzle.is_none() {
        let all_puzzles = puzzles::get_all_puzzles();
        if !all_puzzles.is_empty() {
            puzzle_state.current_puzzle = Some(all_puzzles[0].clone());
        }
    }
    
    // Handle puzzle-specific commands
    let command = terminal.input_buffer.clone();
    if command.starts_with("puzzle") {
        if let Some(puzzle) = &puzzle_state.current_puzzle {
            let mut output = format!("═══ {} ═══\n", puzzle.name);
            output.push_str(&format!("{}\n\n", puzzle.description));
            output.push_str("Input Grid:\n");
            output.push_str(&puzzle.test_input.to_ascii());
            output.push_str(&format!("\nGlyph: {} - {}\n", puzzle.glyph_hint.symbol, puzzle.glyph_hint.meaning));
            
            terminal.output_lines.push(output);
        }
    }
}