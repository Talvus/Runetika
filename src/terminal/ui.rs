use bevy::prelude::*;
use bevy::text::{TextColor, TextFont};
use super::components::*;
use super::{TerminalState, TerminalHistory, LineType};

pub const TERMINAL_WIDTH: f32 = 900.0;
pub const TERMINAL_HEIGHT: f32 = 650.0;
pub const TERMINAL_PADDING: f32 = 25.0;
pub const LINE_HEIGHT: f32 = 22.0;
pub const FONT_SIZE: f32 = 16.0;
pub const HEADER_HEIGHT: f32 = 40.0;

// Deep purple space theme colors
pub const TERMINAL_BG_COLOR: Color = Color::srgba(0.08, 0.02, 0.15, 0.95);  // Deep space purple
pub const TERMINAL_FG_COLOR: Color = Color::srgb(0.85, 0.75, 0.95);  // Soft lavender text
pub const PROMPT_COLOR: Color = Color::srgb(0.6, 0.3, 0.9);  // Bright purple
pub const ERROR_COLOR: Color = Color::srgb(1.0, 0.3, 0.5);  // Hot pink error
pub const SUCCESS_COLOR: Color = Color::srgb(0.3, 0.95, 0.8);  // Cyan success
pub const SYSTEM_COLOR: Color = Color::srgb(0.5, 0.7, 1.0);  // Space blue
pub const GLOW_COLOR: Color = Color::srgba(0.8, 0.3, 1.0, 0.3);  // Purple glow
pub const BORDER_GLOW: Color = Color::srgba(0.6, 0.2, 0.9, 0.8);  // Border purple glow

pub fn setup_terminal(
    mut commands: Commands,
) {
    let text_font = TextFont {
        font_size: FONT_SIZE,
        ..default()
    };
    
    let header_font = TextFont {
        font_size: 18.0,
        ..default()
    };
    
    commands
        .spawn((
            Node {
                width: Val::Px(TERMINAL_WIDTH),
                height: Val::Px(TERMINAL_HEIGHT),
                position_type: PositionType::Absolute,
                left: Val::Percent(50.0),
                top: Val::Percent(50.0),
                margin: UiRect {
                    left: Val::Px(-TERMINAL_WIDTH / 2.0),
                    top: Val::Px(-TERMINAL_HEIGHT / 2.0),
                    ..default()
                },
                flex_direction: FlexDirection::Column,
                padding: UiRect::all(Val::Px(TERMINAL_PADDING)),
                border: UiRect::all(Val::Px(2.0)),
                ..default()
            },
            BackgroundColor(TERMINAL_BG_COLOR),
            BorderColor(BORDER_GLOW),
            BorderRadius::all(Val::Px(12.0)),
            Terminal,
            TerminalBackground,
        ))
        .with_children(|parent| {
            parent.spawn((
                Node {
                    width: Val::Percent(100.0),
                    height: Val::Px(HEADER_HEIGHT),
                    margin: UiRect::bottom(Val::Px(15.0)),
                    align_items: AlignItems::Center,
                    justify_content: JustifyContent::Center,
                    ..default()
                },
                BackgroundColor(Color::srgba(0.15, 0.05, 0.25, 0.8)),
                BorderRadius::top(Val::Px(10.0)),
            ))
            .with_children(|header| {
                header.spawn((
                    Text::new("◆ COSMIC TERMINAL v2.0 ◆"),
                    header_font.clone(),
                    TextColor(Color::srgb(0.9, 0.7, 1.0)),
                ));
            });
            
            parent.spawn((
                Node {
                    width: Val::Percent(100.0),
                    flex_grow: 1.0,
                    flex_direction: FlexDirection::Column,
                    overflow: Overflow::clip(),
                    ..default()
                },
                TerminalDisplay,
            ));
            
            parent.spawn((
                Node {
                    width: Val::Percent(100.0),
                    height: Val::Px(LINE_HEIGHT + 10.0),
                    margin: UiRect::top(Val::Px(10.0)),
                    padding: UiRect::all(Val::Px(5.0)),
                    border: UiRect::all(Val::Px(1.0)),
                    align_items: AlignItems::Center,
                    ..default()
                },
                BackgroundColor(Color::srgba(0.12, 0.05, 0.2, 0.6)),
                BorderColor(Color::srgba(0.7, 0.4, 0.9, 0.5)),
                BorderRadius::all(Val::Px(6.0)),
            ))
            .with_children(|input_area| {
                input_area.spawn((
                    Text::new("❯ "),
                    text_font.clone(),
                    TextColor(Color::srgb(0.8, 0.4, 1.0)),
                    TerminalPrompt,
                ));
                
                input_area.spawn((
                    Text::new(""),
                    text_font.clone(),
                    TextColor(TERMINAL_FG_COLOR),
                    TerminalInputLine,
                ));
                
                input_area.spawn((
                    Text::new("█"),  // Block cursor
                    text_font.clone(),
                    TextColor(Color::srgb(0.9, 0.6, 1.0)),
                    TerminalCursor,
                ));
            });
        });
}

pub fn update_terminal_display(
    mut commands: Commands,
    terminal_history: Res<TerminalHistory>,
    terminal_state: Res<TerminalState>,
    display_query: Query<Entity, With<TerminalDisplay>>,
    children_query: Query<&Children>,
) {
    if !terminal_history.is_changed() && !terminal_state.is_changed() {
        return;
    }
    
    if let Ok(display_entity) = display_query.single() {
        // Clear existing children by despawning them
        if let Ok(children) = children_query.get(display_entity) {
            for child in children.iter() {
                commands.entity(child).despawn();
            }
        }
        
        let visible_lines = (TERMINAL_HEIGHT - 100.0) / LINE_HEIGHT;
        let visible_lines = visible_lines as usize;
        
        let start_index = if terminal_history.lines.len() > visible_lines {
            terminal_history.lines.len().saturating_sub(visible_lines + terminal_state.scroll_offset)
        } else {
            0
        };
        
        let end_index = (start_index + visible_lines).min(terminal_history.lines.len());
        
        commands.entity(display_entity).with_children(|parent| {
            for (index, line) in terminal_history.lines[start_index..end_index].iter().enumerate() {
                let color = match line.line_type {
                    LineType::Input => TERMINAL_FG_COLOR,
                    LineType::Output => TERMINAL_FG_COLOR,
                    LineType::Error => ERROR_COLOR,
                    LineType::System => SYSTEM_COLOR,
                    LineType::Success => SUCCESS_COLOR,
                };
                
                let prefix = match line.line_type {
                    LineType::Input => "❯ ",
                    LineType::System => "❖ ",
                    LineType::Error => "⚠ ",
                    LineType::Success => "✓ ",
                    _ => "",
                };
                
                parent.spawn((
                    Text::new(format!("{}{}", prefix, line.text)),
                    TextFont {
                        font_size: FONT_SIZE,
                        ..default()
                    },
                    TextColor(color),
                    TerminalOutputLine { index },
                ));
            }
        });
    }
}

pub fn animate_cursor(
    time: Res<Time>,
    mut cursor_query: Query<&mut TextColor, With<TerminalCursor>>,
) {
    for mut text_color in cursor_query.iter_mut() {
        let alpha = (time.elapsed_secs() * 2.0).sin() * 0.5 + 0.5;
        text_color.0 = text_color.0.with_alpha(alpha);
    }
}

pub fn animate_terminal_glow(
    time: Res<Time>,
    mut terminal_query: Query<&mut BorderColor, With<Terminal>>,
) {
    for mut border_color in terminal_query.iter_mut() {
        // Create pulsing glow effect
        let glow_intensity = (time.elapsed_secs() * 1.5).sin() * 0.2 + 0.8;
        border_color.0 = Color::srgba(
            0.6 * glow_intensity,
            0.2 * glow_intensity,
            0.9 * glow_intensity,
            0.8
        );
    }
}

pub fn cleanup_terminal(
    mut commands: Commands,
    terminal_query: Query<Entity, With<Terminal>>,
    backdrop_query: Query<Entity, With<super::starfield::TerminalBackdrop>>,
    starfield_query: Query<Entity, With<super::starfield::Starfield>>,
) {
    for entity in terminal_query.iter() {
        commands.entity(entity).despawn();
    }
    for entity in backdrop_query.iter() {
        commands.entity(entity).despawn();
    }
    for entity in starfield_query.iter() {
        commands.entity(entity).despawn();
    }
}