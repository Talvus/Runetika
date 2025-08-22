use bevy::prelude::*;
use bevy::input::keyboard::{KeyboardInput, Key};
use bevy::input::ButtonState;
use super::components::*;
use super::{TerminalState, TerminalHistory, TerminalLine, LineType, CommandRegistry, CommandResult};

pub fn initialize_terminal(
    mut terminal_history: ResMut<TerminalHistory>,
) {
    // Add welcome message
    terminal_history.lines.push(TerminalLine {
        text: "═══════════════════════════════════════".to_string(),
        line_type: LineType::System,
        timestamp: 0.0,
    });
    terminal_history.lines.push(TerminalLine {
        text: "COSMIC TERMINAL v2.0 INITIALIZED".to_string(),
        line_type: LineType::System,
        timestamp: 0.0,
    });
    terminal_history.lines.push(TerminalLine {
        text: "Deep Space Communication Protocol Active".to_string(),
        line_type: LineType::System,
        timestamp: 0.0,
    });
    terminal_history.lines.push(TerminalLine {
        text: "═══════════════════════════════════════".to_string(),
        line_type: LineType::System,
        timestamp: 0.0,
    });
    terminal_history.lines.push(TerminalLine {
        text: "Type 'help' for available commands".to_string(),
        line_type: LineType::Success,
        timestamp: 0.0,
    });
}

pub fn handle_terminal_input(
    mut keyboard_events: EventReader<KeyboardInput>,
    mut terminal_state: ResMut<TerminalState>,
    mut terminal_history: ResMut<TerminalHistory>,
    mut input_text_query: Query<&mut Text, With<TerminalInputLine>>,
    command_registry: Res<CommandRegistry>,
    time: Res<Time>,
) {
    for event in keyboard_events.read() {
        if event.state != ButtonState::Pressed {
            continue;
        }
        
        match &event.logical_key {
            Key::Enter => {
                if !terminal_state.input_buffer.is_empty() {
                    let input = terminal_state.input_buffer.clone();
                    
                    let timestamp = time.elapsed_secs_f64();
                    
                    terminal_history.lines.push(TerminalLine {
                        text: input.clone(),
                        line_type: LineType::Input,
                        timestamp,
                    });
                    
                    terminal_history.command_history.push(input.clone());
                    terminal_history.history_index = None;
                    execute_command(&input, &mut terminal_history, &command_registry, timestamp);
                    
                    terminal_state.input_buffer.clear();
                    terminal_state.cursor_position = 0;
                    
                    if terminal_history.lines.len() > terminal_history.max_lines {
                        terminal_history.lines.drain(0..100);
                    }
                }
            }
            Key::Backspace => {
                if terminal_state.cursor_position > 0 {
                    let pos = terminal_state.cursor_position - 1;
                    terminal_state.input_buffer.remove(pos);
                    terminal_state.cursor_position -= 1;
                }
            }
            Key::Delete => {
                if terminal_state.cursor_position < terminal_state.input_buffer.len() {
                    let pos = terminal_state.cursor_position;
                    terminal_state.input_buffer.remove(pos);
                }
            }
            Key::ArrowLeft => {
                if terminal_state.cursor_position > 0 {
                    terminal_state.cursor_position -= 1;
                }
            }
            Key::ArrowRight => {
                if terminal_state.cursor_position < terminal_state.input_buffer.len() {
                    terminal_state.cursor_position += 1;
                }
            }
            Key::ArrowUp => {
                if !terminal_history.command_history.is_empty() {
                    let new_index = match terminal_history.history_index {
                        None => terminal_history.command_history.len() - 1,
                        Some(i) if i > 0 => i - 1,
                        Some(i) => i,
                    };
                    
                    terminal_history.history_index = Some(new_index);
                    terminal_state.input_buffer = terminal_history.command_history[new_index].clone();
                    terminal_state.cursor_position = terminal_state.input_buffer.len();
                }
            }
            Key::ArrowDown => {
                match terminal_history.history_index {
                    Some(i) if i < terminal_history.command_history.len() - 1 => {
                        terminal_history.history_index = Some(i + 1);
                        terminal_state.input_buffer = terminal_history.command_history[i + 1].clone();
                        terminal_state.cursor_position = terminal_state.input_buffer.len();
                    }
                    Some(_) => {
                        terminal_history.history_index = None;
                        terminal_state.input_buffer.clear();
                        terminal_state.cursor_position = 0;
                    }
                    None => {}
                }
            }
            Key::Home => {
                terminal_state.cursor_position = 0;
            }
            Key::End => {
                terminal_state.cursor_position = terminal_state.input_buffer.len();
            }
            Key::Tab => {
                handle_autocomplete(&mut terminal_state, &command_registry);
            }
            _ => {}
        }
    }
    
    for mut text in input_text_query.iter_mut() {
        text.0 = terminal_state.input_buffer.clone();
    }
}

pub fn handle_terminal_scrolling(
    mut scroll_events: EventReader<bevy::input::mouse::MouseWheel>,
    mut terminal_state: ResMut<TerminalState>,
    terminal_history: Res<TerminalHistory>,
) {
    for event in scroll_events.read() {
        let visible_lines = 25;
        let max_scroll = terminal_history.lines.len().saturating_sub(visible_lines);
        
        if event.y > 0.0 {
            terminal_state.scroll_offset = (terminal_state.scroll_offset + 3).min(max_scroll);
        } else if event.y < 0.0 {
            terminal_state.scroll_offset = terminal_state.scroll_offset.saturating_sub(3);
        }
    }
}

pub fn process_terminal_commands(
    mut keyboard_events: EventReader<KeyboardInput>,
    mut terminal_state: ResMut<TerminalState>,
) {
    for event in keyboard_events.read() {
        if event.state != ButtonState::Pressed {
            continue;
        }
        
        if let Key::Character(ref s) = event.logical_key {
            if let Some(c) = s.chars().next() {
                if !c.is_control() && c != '\n' && c != '\r' && c != '\t' {
                    let pos = terminal_state.cursor_position;
                    terminal_state.input_buffer.insert(pos, c);
                    terminal_state.cursor_position += 1;
                }
            }
        }
    }
}

fn execute_command(
    input: &str,
    terminal_history: &mut TerminalHistory,
    command_registry: &CommandRegistry,
    timestamp: f64,
) {
    let parts: Vec<String> = input.split_whitespace().map(String::from).collect();
    
    if parts.is_empty() {
        return;
    }
    
    let command_name = &parts[0];
    let args = parts[1..].to_vec();
    
    if let Some(command) = command_registry.commands.get(command_name) {
        match command.execute(args, terminal_history) {
            CommandResult::Success(output) => {
                if !output.is_empty() {
                    for line in output.lines() {
                        terminal_history.lines.push(TerminalLine {
                            text: line.to_string(),
                            line_type: LineType::Success,
                            timestamp,
                        });
                    }
                }
            }
            CommandResult::Error(error) => {
                terminal_history.lines.push(TerminalLine {
                    text: format!("Error: {}", error),
                    line_type: LineType::Error,
                    timestamp,
                });
            }
            CommandResult::Continue => {}
        }
    } else {
        terminal_history.lines.push(TerminalLine {
            text: format!("Unknown command: '{}'", command_name),
            line_type: LineType::Error,
            timestamp,
        });
        terminal_history.lines.push(TerminalLine {
            text: "Type 'help' for a list of available commands".to_string(),
            line_type: LineType::System,
            timestamp,
        });
    }
}

fn handle_autocomplete(
    terminal_state: &mut TerminalState,
    command_registry: &CommandRegistry,
) {
    let input = terminal_state.input_buffer.trim();
    
    if input.is_empty() {
        return;
    }
    
    let parts: Vec<&str> = input.split_whitespace().collect();
    
    if parts.len() == 1 {
        let matches: Vec<String> = command_registry.commands.keys()
            .filter(|cmd| cmd.starts_with(parts[0]))
            .cloned()
            .collect();
        
        if matches.len() == 1 {
            terminal_state.input_buffer = matches[0].clone() + " ";
            terminal_state.cursor_position = terminal_state.input_buffer.len();
        }
    }
}