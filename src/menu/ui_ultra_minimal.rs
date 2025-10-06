use bevy::prelude::*;
use super::components::*;
use super::MenuState;

/// Ultra minimal menu - just a camera and colored background
pub fn setup_main_menu(
    mut commands: Commands,
    mut menu_state: ResMut<MenuState>,
) {
    info!("Setting up ultra minimal menu...");
    menu_state.selected_index = 0;
    menu_state.menu_items.clear();
    
    // This is the key fix - spawn a camera!
    commands.spawn((
        Camera2d::default(),
        MainMenu,
        MenuCamera,
        Camera {
            clear_color: ClearColorConfig::Custom(Color::srgb(0.1, 0.1, 0.2)),
            ..default()
        },
    ));
    
    // Simple 2D sprite to show something is working
    commands.spawn((
        Sprite {
            color: Color::srgb(1.0, 1.0, 1.0),
            custom_size: Some(Vec2::new(400.0, 100.0)),
            ..default()
        },
        Transform::from_xyz(0.0, 0.0, 0.0),
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