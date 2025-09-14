/// Papilio Credit System Demo
/// 
/// This example demonstrates the Papilio credit system by simulating
/// puzzle completions and showing how credits are earned and tracked.

use bevy::prelude::*;
use runetika::papilio::{PapilioPlugin, PapilioCredits};
use runetika::arc_engine::{ARCEnginePlugin, PuzzleSolvedEvent};

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_plugins(ARCEnginePlugin)
        .add_plugins(PapilioPlugin)
        .add_systems(Startup, setup)
        .add_systems(Update, simulate_puzzle_solving)
        .run();
}

fn setup(mut commands: Commands, asset_server: Res<AssetServer>) {
    // Camera
    commands.spawn(Camera2dBundle::default());
    
    // UI Text showing instructions
    commands.spawn(
        TextBundle::from_section(
            "Press SPACE to simulate solving a puzzle\nPress M to view milestones\nPress S to sync with Libertalia",
            TextStyle {
                font: asset_server.load("fonts/FiraSans-Bold.ttf"),
                font_size: 24.0,
                color: Color::WHITE,
            },
        )
        .with_style(Style {
            position_type: PositionType::Absolute,
            bottom: Val::Px(20.0),
            left: Val::Px(20.0),
            ..default()
        }),
    );
}

fn simulate_puzzle_solving(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut puzzle_events: EventWriter<PuzzleSolvedEvent>,
    credits: Res<PapilioCredits>,
) {
    // Simulate solving a puzzle when space is pressed
    if keyboard.just_pressed(KeyCode::Space) {
        let puzzle_id = format!("puzzle_{}", rand::random::<u32>() % 100);
        let attempts = (rand::random::<u32>() % 5) + 1;
        let time_taken = rand::random::<f32>() * 120.0 + 10.0;
        
        println!("Simulating puzzle solve:");
        println!("  Puzzle: {}", puzzle_id);
        println!("  Attempts: {}", attempts);
        println!("  Time: {:.1}s", time_taken);
        
        puzzle_events.send(PuzzleSolvedEvent {
            puzzle_id,
            attempts,
            time_taken,
        });
    }
    
    // Show milestones
    if keyboard.just_pressed(KeyCode::KeyM) {
        println!("\n=== Credit Statistics ===");
        println!("Total Balance: {} credits", credits.total_balance());
        println!("Lifetime Earned: {} credits", credits.lifetime_earnings());
        
        let stats = credits.statistics();
        println!("Puzzles Solved: {}", stats.puzzles_solved);
        println!("Perfect Solves: {}", stats.perfect_solves);
        println!("Average Reward: {:.1} credits", stats.average_puzzle_reward);
        println!("Current Streak: {} days", stats.current_streak);
        println!("========================\n");
    }
    
    // Trigger sync
    if keyboard.just_pressed(KeyCode::KeyS) {
        println!("Triggering sync with Libertalia...");
    }
}