use super::pattern::Grid;

#[derive(Debug, Clone)]
pub struct ValidationResult {
    pub valid: bool,
    pub accuracy: f32,
    pub cells_correct: usize,
    pub cells_total: usize,
    pub feedback: String,
}

pub fn validate_solution(player_solution: &Grid, expected: &Grid) -> ValidationResult {
    if player_solution.width != expected.width || player_solution.height != expected.height {
        return ValidationResult {
            valid: false,
            accuracy: 0.0,
            cells_correct: 0,
            cells_total: expected.width * expected.height,
            feedback: "Grid dimensions don't match!".to_string(),
        };
    }
    
    let mut correct = 0;
    let total = expected.width * expected.height;
    
    for y in 0..expected.height {
        for x in 0..expected.width {
            if player_solution.cells[y][x] == expected.cells[y][x] {
                correct += 1;
            }
        }
    }
    
    let accuracy = correct as f32 / total as f32;
    let valid = accuracy >= 1.0;
    
    let feedback = if valid {
        "Perfect! The pattern resonates perfectly!".to_string()
    } else if accuracy >= 0.8 {
        "Very close! The pattern is almost aligned...".to_string()
    } else if accuracy >= 0.5 {
        "You're seeing part of the pattern...".to_string()
    } else {
        "The pattern remains hidden. Try a different approach.".to_string()
    };
    
    ValidationResult {
        valid,
        accuracy,
        cells_correct: correct,
        cells_total: total,
        feedback,
    }
}

fn update_puzzle_state(
    mut puzzle_state: ResMut<super::PuzzleState>,
    keyboard: Res<bevy::prelude::ButtonInput<bevy::prelude::KeyCode>>,
) {
    // Handle puzzle progression
}

fn validate_player_solution(
    puzzle_state: Res<super::PuzzleState>,
    mut events: bevy::prelude::EventWriter<super::PuzzleSolvedEvent>,
) {
    if let (Some(puzzle), Some(solution)) = (&puzzle_state.current_puzzle, &puzzle_state.player_solution) {
        let result = validate_solution(solution, &puzzle.expected_output);
        if result.valid {
            events.send(super::PuzzleSolvedEvent {
                puzzle_id: puzzle.id.clone(),
                attempts: 1,
                time_taken: 0.0,
            });
        }
    }
}