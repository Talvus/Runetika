use bevy::prelude::*;
use super::components::*;
use super::MenuState;

// Space theme colors matching the terminal
pub const MENU_BG_COLOR: Color = Color::srgba(0.02, 0.0, 0.04, 0.98);
pub const TITLE_COLOR: Color = Color::srgb(0.9, 0.7, 1.0);
pub const BUTTON_NORMAL: Color = Color::srgba(0.15, 0.05, 0.25, 0.8);
pub const BUTTON_HOVER: Color = Color::srgba(0.25, 0.1, 0.4, 0.9);
pub const BUTTON_SELECTED: Color = Color::srgba(0.4, 0.15, 0.6, 0.95);
pub const TEXT_COLOR: Color = Color::srgb(0.85, 0.75, 0.95);
pub const GLOW_COLOR: Color = Color::srgba(0.8, 0.3, 1.0, 0.5);

pub fn setup_main_menu(
    mut commands: Commands,
    mut menu_state: ResMut<MenuState>,
) {
    menu_state.selected_index = 0;
    menu_state.menu_items.clear();
    
    // Create menu container
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
            BackgroundColor(MENU_BG_COLOR),
            MainMenu,
            MenuBackground,
        ))
        .with_children(|parent| {
            // Add starfield background
            parent.spawn((
                Node {
                    width: Val::Percent(100.0),
                    height: Val::Percent(100.0),
                    position_type: PositionType::Absolute,
                    ..default()
                },
                MenuStarfield,
            ))
            .with_children(|starfield| {
                // Add animated stars
                for i in 0..100 {
                    let x = (i as f32 * 17.3) % 100.0;
                    let y = (i as f32 * 23.7) % 100.0;
                    let size = 1.0 + (i as f32 * 0.1) % 3.0;
                    
                    starfield.spawn((
                        Node {
                            width: Val::Px(size),
                            height: Val::Px(size),
                            position_type: PositionType::Absolute,
                            left: Val::Percent(x),
                            top: Val::Percent(y),
                            ..default()
                        },
                        BackgroundColor(Color::srgba(0.9, 0.8, 1.0, 0.6)),
                        BorderRadius::all(Val::Percent(50.0)),
                        MenuParticle {
                            velocity: Vec2::new((i as f32 * 0.1) % 0.5 - 0.25, 0.1),
                            lifetime: 10.0,
                        },
                    ));
                }
            });
            
            // Title
            parent.spawn((
                Node {
                    margin: UiRect::bottom(Val::Px(80.0)),
                    ..default()
                },
                MenuTitle,
            ))
            .with_children(|title_parent| {
                title_parent.spawn((
                    Text::new("RUNETIKA"),
                    TextFont {
                        font_size: 80.0,
                        ..default()
                    },
                    TextColor(TITLE_COLOR),
                    Node {
                        position_type: PositionType::Relative,
                        ..default()
                    },
                    MenuGlow {
                        intensity: 1.0,
                        speed: 2.0,
                    },
                ));
                
                title_parent.spawn((
                    Text::new("◆ COSMIC ODYSSEY ◆"),
                    TextFont {
                        font_size: 20.0,
                        ..default()
                    },
                    TextColor(Color::srgb(0.6, 0.5, 0.8)),
                    Node {
                        position_type: PositionType::Absolute,
                        top: Val::Px(70.0),
                        ..default()
                    },
                ));
            });
            
            // Menu buttons
            parent.spawn((
                Node {
                    flex_direction: FlexDirection::Column,
                    align_items: AlignItems::Center,
                    row_gap: Val::Px(20.0),
                    ..default()
                },
            ))
            .with_children(|buttons_parent| {
                let button_configs = vec![
                    ("START GAME", MenuAction::StartGame),
                    ("TERMINAL", MenuAction::OpenTerminal),
                    ("SETTINGS", MenuAction::Settings),
                    ("CREDITS", MenuAction::Credits),
                    ("EXIT", MenuAction::Exit),
                ];
                
                for (index, (text, action)) in button_configs.iter().enumerate() {
                    let button_color = if index == 0 {
                        BUTTON_SELECTED
                    } else {
                        BUTTON_NORMAL
                    };
                    
                    let button_entity = buttons_parent.spawn((
                        Node {
                            width: Val::Px(300.0),
                            height: Val::Px(60.0),
                            justify_content: JustifyContent::Center,
                            align_items: AlignItems::Center,
                            border: UiRect::all(Val::Px(2.0)),
                            ..default()
                        },
                        BackgroundColor(button_color),
                        BorderColor(Color::srgba(0.6, 0.3, 0.9, 0.5)),
                        BorderRadius::all(Val::Px(8.0)),
                        Button,
                        MenuButton { index, action: *action },
                    ))
                    .with_children(|button| {
                        button.spawn((
                            Text::new(*text),
                            TextFont {
                                font_size: 24.0,
                                ..default()
                            },
                            TextColor(TEXT_COLOR),
                        ));
                        
                        if index == 0 {
                            button.spawn((
                                Text::new("▶"),
                                TextFont {
                                    font_size: 20.0,
                                    ..default()
                                },
                                TextColor(Color::srgb(0.9, 0.6, 1.0)),
                                Node {
                                    position_type: PositionType::Absolute,
                                    left: Val::Px(20.0),
                                    ..default()
                                },
                                SelectedMarker,
                            ));
                        }
                    }).id();
                    
                    menu_state.menu_items.push(button_entity);
                }
            });
            
            // Footer
            parent.spawn((
                Text::new("Use ↑↓ or mouse to navigate • Enter to select"),
                TextFont {
                    font_size: 14.0,
                    ..default()
                },
                TextColor(Color::srgba(0.5, 0.4, 0.6, 0.7)),
                Node {
                    position_type: PositionType::Absolute,
                    bottom: Val::Px(30.0),
                    ..default()
                },
            ));
        });
}

pub fn cleanup_main_menu(
    mut commands: Commands,
    menu_query: Query<Entity, With<MainMenu>>,
) {
    for entity in menu_query.iter() {
        commands.entity(entity).despawn();
    }
}