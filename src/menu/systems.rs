use bevy::prelude::*;
use super::components::*;
use super::MenuState;
use super::ui::colors::{BUTTON_NORMAL, BUTTON_HOVER, BUTTON_SELECTED};
use crate::game_state::GameState;

pub fn handle_menu_navigation(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut menu_state: ResMut<MenuState>,
    mut button_query: Query<(&MenuButton, &mut BackgroundColor, &Children)>,
    mut selected_marker_query: Query<&mut Visibility, With<SelectedMarker>>,
    mut next_state: ResMut<NextState<GameState>>,
) {
    if menu_state.is_transitioning {
        return;
    }
    
    let menu_len = menu_state.menu_items.len();
    if menu_len == 0 {
        return;
    }
    
    // Handle navigation
    if keyboard.just_pressed(KeyCode::ArrowUp) || keyboard.just_pressed(KeyCode::KeyW) {
        menu_state.selected_index = (menu_state.selected_index + menu_len - 1) % menu_len;
        update_selection(&menu_state, &mut button_query, &mut selected_marker_query);
    }
    
    if keyboard.just_pressed(KeyCode::ArrowDown) || keyboard.just_pressed(KeyCode::KeyS) {
        menu_state.selected_index = (menu_state.selected_index + 1) % menu_len;
        update_selection(&menu_state, &mut button_query, &mut selected_marker_query);
    }
    
    // Handle selection
    if keyboard.just_pressed(KeyCode::Enter) || keyboard.just_pressed(KeyCode::Space) {
        if let Some(_selected_entity) = menu_state.menu_items.get(menu_state.selected_index) {
            for (button, _, _) in button_query.iter() {
                if button.index == menu_state.selected_index {
                    execute_menu_action(button.action, &mut next_state, &mut menu_state);
                    break;
                }
            }
        }
    }
}

pub fn handle_button_interactions(
    mut interaction_query: Query<
        (&Interaction, &MenuButton, &mut BackgroundColor, &Children),
        Changed<Interaction>,
    >,
    mut menu_state: ResMut<MenuState>,
    mut selected_marker_query: Query<&mut Visibility, With<SelectedMarker>>,
    mut next_state: ResMut<NextState<GameState>>,
) {
    for (interaction, button, mut background, children) in interaction_query.iter_mut() {
        match *interaction {
            Interaction::Pressed => {
                background.0 = BUTTON_SELECTED;
                execute_menu_action(button.action, &mut next_state, &mut menu_state);
            }
            Interaction::Hovered => {
                background.0 = BUTTON_HOVER;
                menu_state.selected_index = button.index;
                
                // Update selected markers
                for child in children.iter() {
                    if let Ok(mut visibility) = selected_marker_query.get_mut(child) {
                        *visibility = Visibility::Visible;
                    }
                }
            }
            Interaction::None => {
                if menu_state.selected_index == button.index {
                    background.0 = BUTTON_SELECTED;
                } else {
                    background.0 = BUTTON_NORMAL;
                }
            }
        }
    }
}

fn update_selection(
    menu_state: &MenuState,
    button_query: &mut Query<(&MenuButton, &mut BackgroundColor, &Children)>,
    selected_marker_query: &mut Query<&mut Visibility, With<SelectedMarker>>,
) {
    for (button, mut background, children) in button_query.iter_mut() {
        if button.index == menu_state.selected_index {
            background.0 = BUTTON_SELECTED;
            
            // Show selected marker
            for child in children.iter() {
                if let Ok(mut visibility) = selected_marker_query.get_mut(child) {
                    *visibility = Visibility::Visible;
                }
            }
        } else {
            background.0 = BUTTON_NORMAL;
            
            // Hide selected marker
            for child in children.iter() {
                if let Ok(mut visibility) = selected_marker_query.get_mut(child) {
                    *visibility = Visibility::Hidden;
                }
            }
        }
    }
}

fn execute_menu_action(
    action: MenuAction,
    next_state: &mut ResMut<NextState<GameState>>,
    menu_state: &mut ResMut<MenuState>,
) {
    menu_state.is_transitioning = true;
    
    match action {
        MenuAction::StartGame => {
            info!("Starting new game...");
            next_state.set(GameState::InGame);
        }
        MenuAction::OpenTerminal => {
            info!("Opening terminal...");
            next_state.set(GameState::InGame);
        }
        MenuAction::Settings => {
            info!("Opening settings...");
            next_state.set(GameState::Settings);
        }
        MenuAction::Credits => {
            info!("Opening credits...");
            next_state.set(GameState::Credits);
        }
        MenuAction::Exit => {
            info!("Exiting game...");
            std::process::exit(0);
        }
    }
}

pub fn update_menu_buttons(
    menu_state: Res<MenuState>,
    mut button_query: Query<(&MenuButton, &mut BackgroundColor)>,
) {
    for (button, mut background) in button_query.iter_mut() {
        if button.index == menu_state.selected_index {
            background.0 = BUTTON_SELECTED;
        }
    }
}

pub fn animate_menu_elements(
    time: Res<Time>,
    mut glow_query: Query<(&mut TextColor, &MenuGlow)>,
    mut particle_query: Query<(&mut Node, &MenuParticle)>,
    mut title_query: Query<&mut Transform, With<MenuTitle>>,
) {
    // Animate glowing text
    for (mut text_color, glow) in glow_query.iter_mut() {
        let intensity = (time.elapsed_secs() * glow.speed).sin() * 0.2 + 0.8;
        text_color.0 = text_color.0.with_alpha(intensity * glow.intensity);
    }
    
    // Animate particles/stars
    for (mut node, particle) in particle_query.iter_mut() {
        if let Val::Percent(mut x) = node.left {
            x += particle.velocity.x * time.delta_secs() * 10.0;
            if x > 100.0 {
                x = -2.0;
            } else if x < -2.0 {
                x = 100.0;
            }
            node.left = Val::Percent(x);
        }
        
        if let Val::Percent(mut y) = node.top {
            y += particle.velocity.y * time.delta_secs() * 10.0;
            if y > 100.0 {
                y = -2.0;
            }
            node.top = Val::Percent(y);
        }
    }
    
    // Subtle title animation
    for mut transform in title_query.iter_mut() {
        let offset = (time.elapsed_secs() * 0.5).sin() * 5.0;
        transform.translation.y = offset;
    }
}