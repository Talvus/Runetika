use bevy::prelude::*;
use bevy::ui::Style;
use super::components::*;
use super::MenuState;

/// Simple menu setup that just gets something on screen
pub fn setup_main_menu(
    mut commands: Commands,
    asset_server: Res<AssetServer>,
    mut menu_state: ResMut<MenuState>,
) {
    menu_state.selected_index = 0;
    menu_state.menu_items.clear();
    
    // Spawn camera for the menu
    commands.spawn((
        Camera2dBundle::default(),
        MainMenu,
        super::components::MenuCamera,
    ));
    
    // Simple root node
    commands
        .spawn((
            NodeBundle {
                style: Style {
                    width: Val::Percent(100.0),
                    height: Val::Percent(100.0),
                    justify_content: JustifyContent::Center,
                    align_items: AlignItems::Center,
                    flex_direction: FlexDirection::Column,
                    ..default()
                },
                background_color: BackgroundColor(Color::srgb(0.02, 0.02, 0.05)),
                ..default()
            },
            MainMenu,
        ))
        .with_children(|parent| {
            // Title
            parent.spawn(TextBundle::from_section(
                "RUNETIKA",
                TextStyle {
                    font_size: 64.0,
                    color: Color::srgb(0.9, 0.9, 1.0),
                    ..default()
                },
            ));
            
            // Menu buttons
            for (index, (text, action)) in [
                ("New Game", MenuAction::StartGame),
                ("Terminal", MenuAction::OpenTerminal),
                ("Settings", MenuAction::Settings),
                ("Credits", MenuAction::Credits),
                ("Exit", MenuAction::Exit),
            ].iter().enumerate() {
                let button_entity = parent.spawn((
                    ButtonBundle {
                        style: Style {
                            width: Val::Px(200.0),
                            height: Val::Px(50.0),
                            margin: UiRect::all(Val::Px(10.0)),
                            justify_content: JustifyContent::Center,
                            align_items: AlignItems::Center,
                            ..default()
                        },
                        background_color: BackgroundColor(Color::srgb(0.1, 0.1, 0.2)),
                        ..default()
                    },
                    MenuButton { index, action: *action },
                )).with_children(|button| {
                    button.spawn(TextBundle::from_section(
                        *text,
                        TextStyle {
                            font_size: 20.0,
                            color: Color::srgb(0.9, 0.9, 1.0),
                            ..default()
                        },
                    ));
                }).id();
                
                menu_state.menu_items.push(button_entity);
            }
        });
}

pub fn cleanup_main_menu(
    mut commands: Commands,
    menu_query: Query<Entity, With<MainMenu>>,
) {
    for entity in menu_query.iter() {
        commands.entity(entity).despawn_recursive();
    }
}