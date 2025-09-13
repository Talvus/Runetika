pub mod types;
pub mod pattern;
pub mod validator;
pub mod puzzles;

use bevy::prelude::*;

pub use types::{ARCPuzzle, Rule, Transformation, Difficulty};
pub use pattern::{Grid, Cell, Pattern, Color as ARCColor};
pub use validator::{validate_solution, ValidationResult};

pub struct ARCEnginePlugin;

impl Plugin for ARCEnginePlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(PuzzleState::default())
            .add_event::<PuzzleSolvedEvent>()
            .add_systems(Update, (
                update_puzzle_state,
                validate_player_solution,
            ));
    }
}

#[derive(Resource, Default)]
pub struct PuzzleState {
    pub current_puzzle: Option<ARCPuzzle>,
    pub player_solution: Option<Grid>,
    pub puzzles_solved: Vec<String>,
    pub current_puzzle_index: usize,
}

#[derive(Event)]
pub struct PuzzleSolvedEvent {
    pub puzzle_id: String,
    pub attempts: u32,
    pub time_taken: f32,
}