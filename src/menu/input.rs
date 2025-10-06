use bevy::prelude::*;
use crate::game_state::GameState;

pub fn handle_basic_input(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut next_state: ResMut<NextState<GameState>>,
    mut exit: EventWriter<AppExit>,
) {
    if keyboard.just_pressed(KeyCode::Enter) || keyboard.just_pressed(KeyCode::Space) {
        info!("Starting game from menu");
        next_state.set(GameState::InGame);
    } else if keyboard.just_pressed(KeyCode::Escape) {
        info!("Exiting game");
        exit.write(AppExit::Success);
    }
}