//! UI module for the main menu system.
//! 
//! This module handles the visual presentation and layout of the game's main menu,
//! including animations, styling, and responsive design elements.

use bevy::prelude::*;
use super::components::*;
use super::MenuState;

/// Color palette for the space-themed menu interface
pub mod colors {
    use bevy::prelude::Color;
    
    /// Deep space background with subtle transparency
    pub const MENU_BG: Color = Color::srgba(0.05, 0.02, 0.15, 0.95);
    
    /// Title text - bright cosmic blue
    pub const TITLE_TEXT: Color = Color::srgb(0.8, 0.9, 1.0);
    
    /// Subtitle text - softer blue
    pub const SUBTITLE_TEXT: Color = Color::srgb(0.6, 0.7, 0.9);
    
    /// Button background - dark with transparency
    pub const BUTTON_BG: Color = Color::srgba(0.1, 0.1, 0.3, 0.8);
    
    /// Button border - cosmic accent
    pub const BUTTON_BORDER: Color = Color::srgb(0.4, 0.6, 1.0);
    
    /// Button text - bright and readable
    pub const BUTTON_TEXT: Color = Color::srgb(0.9, 0.9, 1.0);
    
    /// Selected button highlight
    pub const BUTTON_SELECTED: Color = Color::srgba(0.2, 0.3, 0.6, 0.9);
    
    /// Selected button border
    pub const BUTTON_BORDER_SELECTED: Color = Color::srgb(0.6, 0.8, 1.0);
    
    /// Accent line color
    pub const ACCENT_LINE: Color = Color::srgb(0.5, 0.7, 1.0);
    
    /// Instruction text
    pub const INSTRUCTION_TEXT: Color = Color::srgb(0.5, 0.6, 0.8);
    
    /// Version text
    pub const VERSION_TEXT: Color = Color::srgb(0.4, 0.5, 0.7);
    
    /// Selection indicator
    pub const SELECTION_INDICATOR: Color = Color::srgb(1.0, 0.8, 0.4);
    
    /// Decoration elements
    pub const DECORATION: Color = Color::srgba(0.3, 0.5, 0.8, 0.3);
    
    /// Cosmic orb
    pub const COSMIC_ORB: Color = Color::srgb(0.7, 0.9, 1.0);
}

/// Sets up the main menu UI hierarchy and visual elements.
/// 
/// # Arguments
/// * `commands` - Command buffer for spawning entities
/// * `menu_state` - Mutable reference to the menu state resource
pub fn setup_main_menu(
    mut commands: Commands,
    mut menu_state: ResMut<MenuState>,
) {
    menu_state.selected_index = 0;
    menu_state.menu_items.clear();
    
    // Root container with gradient background
    commands
        .spawn((
            Node {
                width: Val::Percent(100.0),
                height: Val::Percent(100.0),
                position_type: PositionType::Absolute,
                flex_direction: FlexDirection::Column,
                justify_content: JustifyContent::Center,
                align_items: AlignItems::Center,
                ..default()
            },
            BackgroundColor(colors::MENU_BG),
            MainMenu,
            MenuBackground,
        ))
        .with_children(|parent| {
            // Title section
            parent.spawn((
                Node {
                    flex_direction: FlexDirection::Column,
                    align_items: AlignItems::Center,
                    margin: UiRect {
                        bottom: Val::Px(40.0),
                        ..default()
                    },
                    ..default()
                },
            ))
            .with_children(|title_parent| {
                // Main title
                title_parent.spawn((
                    Text::new("RUNETIKA"),
                    TextFont {
                        font_size: 48.0,
                        ..default()
                    },
                    TextColor(colors::TITLE_TEXT),
                ));
                
                // Subtitle
                title_parent.spawn((
                    Text::new("Cosmic Odyssey"),
                    TextFont {
                        font_size: 18.0,
                        ..default()
                    },
                    TextColor(colors::SUBTITLE_TEXT),
                ));
            });
            
            // Menu buttons section
            parent.spawn((
                Node {
                    flex_direction: FlexDirection::Column,
                    align_items: AlignItems::Center,
                    row_gap: Val::Px(15.0),
                    padding: UiRect::all(Val::Px(20.0)),
                    ..default()
                },
            ))
            .with_children(|buttons_parent| {
                let button_configs = vec![
                    ("⚡ NEW GAME", MenuAction::StartGame, "Begin your cosmic journey"),
                    ("💻 TERMINAL", MenuAction::OpenTerminal, "Access the command interface"),
                    ("⚙️ SETTINGS", MenuAction::Settings, "Configure your experience"),
                    ("👥 CREDITS", MenuAction::Credits, "Meet the creators"),
                    ("🚪 EXIT", MenuAction::Exit, "Leave the cosmos"),
                ];
                
                for (index, (text, action, _tooltip)) in button_configs.iter().enumerate() {
                    let is_selected = index == menu_state.selected_index;
                    let button_bg = if is_selected { colors::BUTTON_SELECTED } else { colors::BUTTON_BG };
                    let border_color = if is_selected { colors::BUTTON_BORDER_SELECTED } else { colors::BUTTON_BORDER };
                    
                    let button_entity = buttons_parent.spawn((
                        Button,
                        Node {
                            width: Val::Px(250.0),
                            height: Val::Px(50.0),
                            border: UiRect::all(Val::Px(2.0)),
                            justify_content: JustifyContent::Center,
                            align_items: AlignItems::Center,
                            ..default()
                        },
                        BorderColor(border_color),
                        BackgroundColor(button_bg),
                        MenuButton {
                            index,
                            action: action.clone(),
                        },
                    ))
                    .with_children(|button| {
                        button.spawn((
                            Text::new(*text),
                            TextFont {
                                font_size: 16.0,
                                ..default()
                            },
                            TextColor(colors::BUTTON_TEXT),
                        ));
                    }).id();
                    
                    menu_state.menu_items.push(button_entity);
                }
            });
            
            // Footer section
            parent.spawn((
                Node {
                    position_type: PositionType::Absolute,
                    bottom: Val::Px(20.0),
                    flex_direction: FlexDirection::Column,
                    align_items: AlignItems::Center,
                    ..default()
                },
            ))
            .with_children(|footer| {
                footer.spawn((
                    Text::new("Use ↑↓ Arrow Keys or Mouse • Enter/Click to Select • ESC to Exit"),
                    TextFont {
                        font_size: 12.0,
                        ..default()
                    },
                    TextColor(colors::INSTRUCTION_TEXT),
                ));
                
                footer.spawn((
                    Text::new("Version 0.1.0 - Pre-Alpha"),
                    TextFont {
                        font_size: 10.0,
                        ..default()
                    },
                    TextColor(colors::VERSION_TEXT),
                ));
            });
        });
}

/// Cleans up all menu UI elements when transitioning away from the main menu
pub fn cleanup_main_menu(
    mut commands: Commands,
    menu_query: Query<Entity, With<MainMenu>>,
) {
    for entity in menu_query.iter() {
        commands.entity(entity).despawn();
    }
}