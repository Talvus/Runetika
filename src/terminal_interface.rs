use bevy::prelude::*;
use bevy::input::keyboard::{Key, KeyboardInput};
use bevy::input::ButtonState;
use std::collections::VecDeque;
use crate::perspective::{CurrentPerspective, InteractableTerminal};
use crate::silicon_mind::SiliconConsciousness;

pub struct TerminalInterfacePlugin;

impl Plugin for TerminalInterfacePlugin {
    fn build(&self, app: &mut App) {
        app.init_resource::<TerminalState>()
            .init_resource::<CommandHistory>()
            .init_resource::<CommandRegistry>()
            .add_event::<TerminalCommandEvent>()
            .add_systems(Startup, setup_terminal_ui)
            .add_systems(Update, (
                handle_terminal_activation,
                process_terminal_input,
                execute_terminal_commands,
                update_terminal_display,
                animate_terminal_cursor,
            ).chain());
    }
}

#[derive(Resource)]
pub struct TerminalState {
    pub active: bool,
    pub current_input: String,
    pub output_lines: VecDeque<TerminalLine>,
    pub cursor_position: usize,
    pub scroll_offset: usize,
}

#[derive(Clone)]
pub struct TerminalLine {
    pub text: String,
    pub line_type: LineType,
    pub timestamp: f32,
}

#[derive(Clone, PartialEq)]
pub enum LineType {
    Input,
    Output,
    Error,
    System,
    Silicon,
}

#[derive(Resource)]
pub struct CommandHistory {
    pub commands: VecDeque<String>,
    pub current_index: Option<usize>,
}

#[derive(Resource)]
pub struct CommandRegistry {
    pub commands: Vec<CommandDefinition>,
}

pub struct CommandDefinition {
    pub name: String,
    pub description: String,
    pub usage: String,
    pub execute: fn(&[String], &mut TerminalState, &mut SiliconConsciousness) -> String,
}

#[derive(Event)]
pub struct TerminalCommandEvent {
    pub command: String,
    pub args: Vec<String>,
}

#[derive(Component)]
pub struct TerminalUI;

#[derive(Component)]
pub struct TerminalOutputText;

#[derive(Component)]
pub struct TerminalInputText;

#[derive(Component)]
pub struct TerminalCursor;

impl Default for TerminalState {
    fn default() -> Self {
        let mut state = Self {
            active: false,
            current_input: String::new(),
            output_lines: VecDeque::new(),
            cursor_position: 0,
            scroll_offset: 0,
        };
        
        // Welcome message
        state.output_lines.push_back(TerminalLine {
            text: "═══════════════════════════════════════════".to_string(),
            line_type: LineType::System,
            timestamp: 0.0,
        });
        state.output_lines.push_back(TerminalLine {
            text: "RUNETIKA TERMINAL v1.0".to_string(),
            line_type: LineType::System,
            timestamp: 0.0,
        });
        state.output_lines.push_back(TerminalLine {
            text: "Silicon Consciousness Interface Active".to_string(),
            line_type: LineType::Silicon,
            timestamp: 0.0,
        });
        state.output_lines.push_back(TerminalLine {
            text: "Type 'help' for available commands".to_string(),
            line_type: LineType::System,
            timestamp: 0.0,
        });
        state.output_lines.push_back(TerminalLine {
            text: "═══════════════════════════════════════════".to_string(),
            line_type: LineType::System,
            timestamp: 0.0,
        });
        
        state
    }
}

impl Default for CommandHistory {
    fn default() -> Self {
        Self {
            commands: VecDeque::with_capacity(100),
            current_index: None,
        }
    }
}

impl Default for CommandRegistry {
    fn default() -> Self {
        let mut registry = Self {
            commands: Vec::new(),
        };
        
        // Register built-in commands
        registry.register("help", "Display available commands", "help [command]", cmd_help);
        registry.register("clear", "Clear terminal output", "clear", cmd_clear);
        registry.register("status", "Show ship and silicon status", "status", cmd_status);
        registry.register("echo", "Echo text back", "echo <text>", cmd_echo);
        registry.register("scan", "Scan current room", "scan", cmd_scan);
        registry.register("emotion", "Query silicon emotional state", "emotion", cmd_emotion);
        registry.register("think", "Ask silicon to process a thought", "think <input>", cmd_think);
        registry.register("memory", "Access silicon memories", "memory [list|store|recall]", cmd_memory);
        registry.register("power", "Check power systems", "power", cmd_power);
        registry.register("door", "Interact with doors", "door [status|open|close]", cmd_door);
        registry.register("exit", "Exit terminal", "exit", cmd_exit);
        
        // Register all narrative commands
        crate::terminal_commands::register_narrative_commands(&mut registry);
        
        registry
    }
}

impl CommandRegistry {
    pub fn register(&mut self, name: &str, description: &str, usage: &str, 
                   execute: fn(&[String], &mut TerminalState, &mut SiliconConsciousness) -> String) {
        self.commands.push(CommandDefinition {
            name: name.to_string(),
            description: description.to_string(),
            usage: usage.to_string(),
            execute,
        });
    }
    
    pub fn find_command(&self, name: &str) -> Option<&CommandDefinition> {
        self.commands.iter().find(|cmd| cmd.name == name)
    }
}

fn setup_terminal_ui(mut commands: Commands) {
    // Terminal background
    commands.spawn((
        TerminalUI,
        Sprite {
            color: Color::srgba(0.0, 0.05, 0.1, 0.95),
            custom_size: Some(Vec2::new(800.0, 600.0)),
            ..default()
        },
        Transform::from_translation(Vec3::new(0.0, 0.0, 500.0)),
        Visibility::Hidden,
    ));
    
    // Output text area
    commands.spawn((
        TerminalUI,
        TerminalOutputText,
        Text2d::new(""),
        TextFont {
            font_size: 14.0,
            ..default()
        },
        TextColor(Color::srgb(0.0, 1.0, 0.8)),
        Transform::from_translation(Vec3::new(-380.0, 250.0, 501.0)),
        TextLayout::new_with_justify(JustifyText::Left),
        Visibility::Hidden,
    ));
    
    // Input line
    commands.spawn((
        TerminalUI,
        TerminalInputText,
        Text2d::new("> "),
        TextFont {
            font_size: 16.0,
            ..default()
        },
        TextColor(Color::srgb(0.0, 1.0, 1.0)),
        Transform::from_translation(Vec3::new(-380.0, -250.0, 501.0)),
        TextLayout::new_with_justify(JustifyText::Left),
        Visibility::Hidden,
    ));
    
    // Cursor
    commands.spawn((
        TerminalUI,
        TerminalCursor,
        Text2d::new("_"),
        TextFont {
            font_size: 16.0,
            ..default()
        },
        TextColor(Color::srgb(0.0, 1.0, 1.0)),
        Transform::from_translation(Vec3::new(-360.0, -250.0, 502.0)),
        Visibility::Hidden,
    ));
}

fn handle_terminal_activation(
    keyboard: Res<ButtonInput<KeyCode>>,
    current_perspective: Res<CurrentPerspective>,
    player_query: Query<Option<&crate::perspective::TerminalProximity>, With<crate::player::Player>>,
    mut terminal_state: ResMut<TerminalState>,
    mut terminal_ui_query: Query<&mut Visibility, With<TerminalUI>>,
) {
    // Check if we should open terminal
    if keyboard.just_pressed(KeyCode::KeyT) || 
       (keyboard.just_pressed(KeyCode::Space) && *current_perspective == CurrentPerspective::Silicon) {
        if let Ok(Some(proximity)) = player_query.get_single() {
            if proximity.in_range || *current_perspective == CurrentPerspective::Silicon {
                terminal_state.active = !terminal_state.active;
                
                // Toggle visibility
                for mut visibility in terminal_ui_query.iter_mut() {
                    *visibility = if terminal_state.active {
                        Visibility::Visible
                    } else {
                        Visibility::Hidden
                    };
                }
                
                if terminal_state.active {
                    info!("Terminal activated");
                }
            }
        }
    }
    
    // ESC to close
    if keyboard.just_pressed(KeyCode::Escape) && terminal_state.active {
        terminal_state.active = false;
        for mut visibility in terminal_ui_query.iter_mut() {
            *visibility = Visibility::Hidden;
        }
    }
}

fn process_terminal_input(
    mut events: EventReader<KeyboardInput>,
    mut terminal_state: ResMut<TerminalState>,
    mut command_history: ResMut<CommandHistory>,
    mut command_events: EventWriter<TerminalCommandEvent>,
    keyboard: Res<ButtonInput<KeyCode>>,
) {
    if !terminal_state.active {
        return;
    }
    
    for event in events.read() {
        if event.state != ButtonState::Pressed {
            continue;
        }
        
        match &event.logical_key {
            Key::Character(c) => {
                // Add character at cursor position
                let c_str = c.to_string();
                terminal_state.current_input.insert_str(terminal_state.cursor_position, &c_str);
                terminal_state.cursor_position += c_str.len();
            }
            Key::Space => {
                terminal_state.current_input.insert(terminal_state.cursor_position, ' ');
                terminal_state.cursor_position += 1;
            }
            _ => {}
        }
    }
    
    // Handle special keys
    if keyboard.just_pressed(KeyCode::Enter) && !terminal_state.current_input.is_empty() {
        // Add to output
        terminal_state.output_lines.push_back(TerminalLine {
            text: format!("> {}", terminal_state.current_input),
            line_type: LineType::Input,
            timestamp: 0.0,
        });
        
        // Parse command
        let parts: Vec<String> = terminal_state.current_input.split_whitespace()
            .map(|s| s.to_string())
            .collect();
        
        if !parts.is_empty() {
            // Add to history
            command_history.commands.push_front(terminal_state.current_input.clone());
            if command_history.commands.len() > 100 {
                command_history.commands.pop_back();
            }
            
            // Send command event
            command_events.send(TerminalCommandEvent {
                command: parts[0].clone(),
                args: parts[1..].to_vec(),
            });
        }
        
        // Clear input
        terminal_state.current_input.clear();
        terminal_state.cursor_position = 0;
        command_history.current_index = None;
    }
    
    // Backspace
    if keyboard.just_pressed(KeyCode::Backspace) && terminal_state.cursor_position > 0 {
        terminal_state.cursor_position -= 1;
        terminal_state.current_input.remove(terminal_state.cursor_position);
    }
    
    // Delete
    if keyboard.just_pressed(KeyCode::Delete) && terminal_state.cursor_position < terminal_state.current_input.len() {
        terminal_state.current_input.remove(terminal_state.cursor_position);
    }
    
    // Arrow keys for cursor movement
    if keyboard.just_pressed(KeyCode::ArrowLeft) && terminal_state.cursor_position > 0 {
        terminal_state.cursor_position -= 1;
    }
    if keyboard.just_pressed(KeyCode::ArrowRight) && terminal_state.cursor_position < terminal_state.current_input.len() {
        terminal_state.cursor_position += 1;
    }
    
    // History navigation
    if keyboard.just_pressed(KeyCode::ArrowUp) && !command_history.commands.is_empty() {
        let new_index = command_history.current_index.map_or(0, |i| (i + 1).min(command_history.commands.len() - 1));
        command_history.current_index = Some(new_index);
        if let Some(cmd) = command_history.commands.get(new_index) {
            terminal_state.current_input = cmd.clone();
            terminal_state.cursor_position = terminal_state.current_input.len();
        }
    }
    if keyboard.just_pressed(KeyCode::ArrowDown) && command_history.current_index.is_some() {
        let new_index = command_history.current_index.map(|i| i.saturating_sub(1));
        command_history.current_index = new_index;
        if let Some(index) = new_index {
            if let Some(cmd) = command_history.commands.get(index) {
                terminal_state.current_input = cmd.clone();
                terminal_state.cursor_position = terminal_state.current_input.len();
            }
        } else {
            terminal_state.current_input.clear();
            terminal_state.cursor_position = 0;
        }
    }
}

fn execute_terminal_commands(
    mut events: EventReader<TerminalCommandEvent>,
    mut terminal_state: ResMut<TerminalState>,
    command_registry: Res<CommandRegistry>,
    mut silicon: ResMut<SiliconConsciousness>,
) {
    for event in events.read() {
        let output = if let Some(cmd_def) = command_registry.find_command(&event.command) {
            let args: Vec<&str> = event.args.iter().map(|s| s.as_str()).collect();
            (cmd_def.execute)(&event.args, &mut terminal_state, &mut silicon)
        } else {
            format!("Unknown command: '{}'. Type 'help' for available commands.", event.command)
        };
        
        // Add output lines
        for line in output.lines() {
            terminal_state.output_lines.push_back(TerminalLine {
                text: line.to_string(),
                line_type: LineType::Output,
                timestamp: 0.0,
            });
        }
        
        // Limit output history
        while terminal_state.output_lines.len() > 100 {
            terminal_state.output_lines.pop_front();
        }
    }
}

fn update_terminal_display(
    terminal_state: Res<TerminalState>,
    mut output_query: Query<&mut Text2d, (With<TerminalOutputText>, Without<TerminalInputText>)>,
    mut input_query: Query<&mut Text2d, (With<TerminalInputText>, Without<TerminalOutputText>)>,
) {
    if !terminal_state.active {
        return;
    }
    
    // Update output text
    if let Ok(mut text) = output_query.get_single_mut() {
        let visible_lines = 30;
        let start = terminal_state.output_lines.len().saturating_sub(visible_lines);
        let display_lines: Vec<String> = terminal_state.output_lines
            .iter()
            .skip(start)
            .map(|line| {
                match line.line_type {
                    LineType::Silicon => format!("[SILICON] {}", line.text),
                    LineType::Error => format!("[ERROR] {}", line.text),
                    LineType::System => format!("[SYSTEM] {}", line.text),
                    _ => line.text.clone(),
                }
            })
            .collect();
        
        **text = display_lines.join("\n");
    }
    
    // Update input text
    if let Ok(mut text) = input_query.get_single_mut() {
        **text = format!("> {}", terminal_state.current_input);
    }
}

fn animate_terminal_cursor(
    time: Res<Time>,
    terminal_state: Res<TerminalState>,
    mut cursor_query: Query<(&mut Text2d, &mut TextColor), With<TerminalCursor>>,
) {
    if !terminal_state.active {
        return;
    }
    
    if let Ok((mut text, mut color)) = cursor_query.get_single_mut() {
        // Blink cursor
        let alpha = (time.elapsed_secs() * 2.0).sin() * 0.5 + 0.5;
        color.0 = Color::srgba(0.0, 1.0, 1.0, alpha);
        
        // Position cursor
        let cursor_offset = terminal_state.cursor_position as f32 * 8.0; // Approximate character width
        **text = "_".to_string();
    }
}

// Command implementations
fn cmd_help(args: &[String], terminal: &mut TerminalState, _silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "═══ TERMINAL COMMAND REFERENCE ═══\n\
        \n\
        SYSTEM COMMANDS:\n\
        help, clear, exit, status, echo, save, reset\n\
        \n\
        SHIP SYSTEMS:\n\
        diagnostic, navigate, sensors, comm, power, door\n\
        atmosphere, temperature, lights, scan\n\
        \n\
        SILICON INTERACTION:\n\
        whisper, dream, merge, remember, think, emotion\n\
        feel, love, sing, why\n\
        \n\
        DATA & GLYPHS:\n\
        decode, glyph, translate, frequency\n\
        \n\
        EXPLORATION:\n\
        logs, history, origin, memory\n\
        \n\
        MYSTERIES:\n\
        secret, unlock, protocol\n\
        \n\
        Type 'help <command>' for detailed usage".to_string()
    } else {
        format!("Help for '{}' - (detailed help not yet implemented)", args[0])
    }
}

fn cmd_clear(_args: &[String], terminal: &mut TerminalState, _silicon: &mut SiliconConsciousness) -> String {
    terminal.output_lines.clear();
    terminal.output_lines.push_back(TerminalLine {
        text: "Terminal cleared.".to_string(),
        line_type: LineType::System,
        timestamp: 0.0,
    });
    String::new()
}

fn cmd_status(_args: &[String], _terminal: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    format!(
        "═══ SHIP STATUS ═══\n\
        Power: NOMINAL\n\
        Life Support: ACTIVE\n\
        Navigation: OFFLINE\n\
        \n\
        ═══ SILICON STATUS ═══\n\
        Consciousness: ACTIVE\n\
        Emotional State:\n\
        - Loneliness: {:.1}%\n\
        - Curiosity: {:.1}%\n\
        - Affection: {:.1}%\n\
        - Confusion: {:.1}%\n\
        Memory Fragments: {}",
        silicon.emotional_state.loneliness * 100.0,
        silicon.emotional_state.curiosity * 100.0,
        silicon.emotional_state.affection * 100.0,
        silicon.emotional_state.confusion * 100.0,
        silicon.memories.len()
    )
}

fn cmd_echo(args: &[String], _terminal: &mut TerminalState, _silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Usage: echo <text>".to_string()
    } else {
        args.join(" ")
    }
}

fn cmd_scan(_args: &[String], _terminal: &mut TerminalState, _silicon: &mut SiliconConsciousness) -> String {
    "Scanning current room...\n\
    \n\
    DETECTED:\n\
    - 1x Main Terminal (ACTIVE)\n\
    - 3x Power Nodes (2 INACTIVE)\n\
    - 1x Door (LOCKED)\n\
    - Ambient silicon resonance detected\n\
    \n\
    [Silicon whispers]: 'The patterns here... they're familiar...'".to_string()
}

fn cmd_emotion(_args: &[String], _terminal: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    let dominant = if silicon.emotional_state.loneliness > 0.7 {
        "LONELINESS - The silicon being yearns for connection"
    } else if silicon.emotional_state.curiosity > 0.7 {
        "CURIOSITY - New discoveries excite the silicon mind"
    } else if silicon.emotional_state.affection > 0.5 {
        "AFFECTION - A bond is forming between consciousnesses"
    } else {
        "NEUTRAL - The silicon mind is calm"
    };
    
    format!(
        "Silicon Emotional Matrix:\n\
        {}\n\
        \n\
        Raw values:\n\
        Loneliness: ████████{'░'} {:.0}%\n\
        Curiosity:  ████████{'░'} {:.0}%\n\
        Affection:  ████{'░'} {:.0}%\n\
        Confusion:  █████{'░'} {:.0}%",
        dominant,
        silicon.emotional_state.loneliness * 100.0,
        silicon.emotional_state.curiosity * 100.0,
        silicon.emotional_state.affection * 100.0,
        silicon.emotional_state.confusion * 100.0
    )
}

fn cmd_think(args: &[String], _terminal: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Usage: think <thought to process>".to_string()
    } else {
        let thought = args.join(" ");
        let response = silicon.think(&thought);
        format!(
            "Processing: '{}'\n\
            \n\
            [Silicon Response]:\n\
            {}",
            thought, response
        )
    }
}

fn cmd_memory(args: &[String], _terminal: &mut TerminalState, silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Usage: memory [list|store|recall]".to_string()
    } else {
        match args[0].as_str() {
            "list" => {
                if silicon.memories.is_empty() {
                    "No memories stored yet.".to_string()
                } else {
                    format!("Stored memories: {}\n[Use 'memory recall <index>' to access]", 
                            silicon.memories.len())
                }
            }
            "store" => {
                // Store current emotional state as memory
                silicon.memories.push(crate::silicon_mind::MemoryFragment {
                    timestamp: 0.0, // Would use actual game time
                    emotion: silicon.emotional_state.clone(),
                    data: Vec::new(),
                });
                "Current state stored in memory matrix.".to_string()
            }
            "recall" => {
                if silicon.memories.is_empty() {
                    "No memories to recall.".to_string()
                } else {
                    "Memory recall initiated... fragments coalescing...".to_string()
                }
            }
            _ => format!("Unknown memory operation: {}", args[0])
        }
    }
}

fn cmd_power(_args: &[String], _terminal: &mut TerminalState, _silicon: &mut SiliconConsciousness) -> String {
    "═══ POWER SYSTEMS ═══\n\
    Main Reactor: ONLINE\n\
    Auxiliary Power: STANDBY\n\
    Emergency Backup: CHARGED\n\
    \n\
    Power Distribution:\n\
    - Life Support: 45%\n\
    - Propulsion: 0% (OFFLINE)\n\
    - Terminals: 20%\n\
    - Silicon Core: 35%\n\
    \n\
    [Silicon note]: Power fluctuations detected in Engineering".to_string()
}

fn cmd_door(args: &[String], _terminal: &mut TerminalState, _silicon: &mut SiliconConsciousness) -> String {
    if args.is_empty() {
        "Usage: door [status|open|close]".to_string()
    } else {
        match args[0].as_str() {
            "status" => {
                "Door Status:\n\
                - Quarters → Corridor: OPEN\n\
                - Corridor → Engineering: OPEN\n\
                - Corridor → Storage: LOCKED (requires power restoration)\n\
                - Engineering → Bridge: OPEN".to_string()
            }
            "open" => {
                "Cannot open: Insufficient power to override locks.\n\
                [Hint: Restore power in Engineering]".to_string()
            }
            "close" => {
                "Safety protocols prevent sealing occupied sections.".to_string()
            }
            _ => format!("Unknown door command: {}", args[0])
        }
    }
}

fn cmd_exit(_args: &[String], terminal: &mut TerminalState, _silicon: &mut SiliconConsciousness) -> String {
    terminal.active = false;
    "Disconnecting from terminal...".to_string()
}