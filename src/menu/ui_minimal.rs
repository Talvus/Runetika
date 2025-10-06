use bevy::prelude::*;
use super::components::*;
use super::MenuState;

/// Minimal menu setup that just displays text
pub fn setup_main_menu(
    mut commands: Commands,
    mut menu_state: ResMut<MenuState>,
) {
    menu_state.selected_index = 0;
    menu_state.menu_items.clear();
    
    // Spawn camera for the menu - this is the key fix for blank screen
    commands.spawn((
        Camera2dBundle::default(),
        MainMenu,
        MenuCamera,
    ));
    
    // Just spawn some text to prove the menu is working
    commands.spawn((
        Text2dBundle {
            text: Text::from_section(
                "RUNETIKA - MAIN MENU\n\nPress Enter to start\nPress Escape to exit",
                TextStyle {
                    font: Handle::<Font>::default(),
                    font_size: 32.0,
                    color: Color::WHITE,
                },
            ),
            ..default()
        },
        MainMenu,
    ));
}

pub fn cleanup_main_menu(
    mut commands: Commands,
    menu_query: Query<Entity, With<MainMenu>>,
) {
    for entity in menu_query.iter() {
        commands.entity(entity).despawn();
    }
}