//! Maze UI components
//!
//! Provides the completion counter and maze status display.

use bevy::prelude::*;
use super::{MazeState, knossos::KnossosMazeConfig};

/// Component marking the maze completion UI
#[derive(Component)]
pub struct MazeCompletionUI;

/// Component for the algorithm display
#[derive(Component)]
pub struct MazeAlgorithmUI;

/// Component for the difficulty display
#[derive(Component)]
pub struct MazeDifficultyUI;

/// Spawn the maze UI elements
pub fn spawn_maze_ui(commands: &mut Commands) {
    // Container for maze UI
    commands.spawn((
        MazeCompletionUI,
        Node {
            position_type: PositionType::Absolute,
            top: Val::Px(10.0),
            right: Val::Px(10.0),
            flex_direction: FlexDirection::Column,
            align_items: AlignItems::End,
            row_gap: Val::Px(5.0),
            padding: UiRect::all(Val::Px(10.0)),
            ..default()
        },
        BackgroundColor(Color::srgba(0.0, 0.0, 0.0, 0.7)),
    )).with_children(|parent| {
        // Completion counter
        parent.spawn((
            Text::new("Mazes: 0"),
            TextFont {
                font_size: 18.0,
                ..default()
            },
            TextColor(Color::srgb(0.3, 1.0, 0.3)),
            MazeCompletionUI,
        ));

        // Algorithm display
        parent.spawn((
            Text::new("Algorithm: -"),
            TextFont {
                font_size: 14.0,
                ..default()
            },
            TextColor(Color::srgb(0.7, 0.7, 0.9)),
            MazeAlgorithmUI,
        ));

        // Difficulty display
        parent.spawn((
            Text::new("Difficulty: -"),
            TextFont {
                font_size: 14.0,
                ..default()
            },
            TextColor(Color::srgb(0.9, 0.7, 0.3)),
            MazeDifficultyUI,
        ));
    });
}

/// Despawn maze UI elements
pub fn despawn_maze_ui(
    commands: &mut Commands,
    ui_query: Query<Entity, With<MazeCompletionUI>>,
) {
    for entity in ui_query.iter() {
        commands.entity(entity).despawn();
    }
}

/// Update the completion counter text
pub fn update_maze_ui(
    maze_state: Res<MazeState>,
    config: Res<KnossosMazeConfig>,
    mut completion_query: Query<&mut Text, (With<MazeCompletionUI>, Without<MazeAlgorithmUI>, Without<MazeDifficultyUI>)>,
    mut algorithm_query: Query<&mut Text, (With<MazeAlgorithmUI>, Without<MazeCompletionUI>, Without<MazeDifficultyUI>)>,
    mut difficulty_query: Query<&mut Text, (With<MazeDifficultyUI>, Without<MazeCompletionUI>, Without<MazeAlgorithmUI>)>,
) {
    // Only update when in maze
    if !maze_state.in_maze {
        return;
    }

    // Update completion counter
    for mut text in completion_query.iter_mut() {
        **text = format!("Mazes: {}", maze_state.completions);
    }

    // Update algorithm name
    for mut text in algorithm_query.iter_mut() {
        **text = format!("Algorithm: {}", config.algorithm.name());
    }

    // Update difficulty
    for mut text in difficulty_query.iter_mut() {
        let difficulty = config.algorithm.difficulty();
        let stars = "★".repeat(difficulty as usize) + &"☆".repeat(10 - difficulty as usize);
        **text = format!("Difficulty: {}", stars);
    }
}

/// Show a completion notification
pub fn show_completion_notification(commands: &mut Commands, completions: u32) {
    commands.spawn((
        CompletionNotification {
            timer: Timer::from_seconds(3.0, TimerMode::Once),
        },
        Text::new(format!("🎉 Maze #{} Complete!", completions)),
        TextFont {
            font_size: 32.0,
            ..default()
        },
        TextColor(Color::srgb(1.0, 0.9, 0.3)),
        Node {
            position_type: PositionType::Absolute,
            top: Val::Percent(30.0),
            left: Val::Percent(50.0),
            ..default()
        },
    ));
}

/// Component for temporary completion notification
#[derive(Component)]
pub struct CompletionNotification {
    pub timer: Timer,
}

/// System to fade out and despawn completion notifications
pub fn update_completion_notifications(
    mut commands: Commands,
    time: Res<Time>,
    mut notification_query: Query<(Entity, &mut CompletionNotification, &mut TextColor)>,
) {
    for (entity, mut notification, mut color) in notification_query.iter_mut() {
        notification.timer.tick(time.delta());

        // Fade out over the last second
        let remaining = notification.timer.remaining_secs();
        if remaining < 1.0 {
            color.0 = color.0.with_alpha(remaining);
        }

        if notification.timer.just_finished() {
            commands.entity(entity).despawn();
        }
    }
}
