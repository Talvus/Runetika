/// Papilio Credit System - Reward system for puzzle completion
/// 
/// This module handles the integration with the Papilio credit system on Libertalia,
/// rewarding players for solving ARC puzzles and other challenges in Runetika.
/// 
/// # Architecture Philosophy
/// The credit system is designed to be:
/// - **Modular**: Can integrate with any external credit system
/// - **Fair**: Rewards based on puzzle difficulty and performance
/// - **Persistent**: Credits are saved and synchronized
/// - **Transparent**: Players always know what they're earning

pub mod types;
pub mod persistence;
pub mod rewards;
pub mod integration;
pub mod ui;

use bevy::prelude::*;
use crate::arc_engine::{PuzzleSolvedEvent, Difficulty};

pub use types::{PapilioCredits, CreditTransaction, CreditSource};
pub use rewards::{RewardCalculator, RewardMultiplier};
pub use integration::{LibertaliaSyncStatus, PapilioIntegration};
pub use ui::CreditNotification;

/// Main plugin for the Papilio credit system
pub struct PapilioPlugin;

impl Plugin for PapilioPlugin {
    fn build(&self, app: &mut App) {
        app
            // Resources
            .insert_resource(PapilioCredits::default())
            .insert_resource(RewardCalculator::default())
            .insert_resource(LibertaliaSyncStatus::default())
            
            // Events
            .add_event::<CreditEarnedEvent>()
            .add_event::<CreditSyncEvent>()
            .add_event::<CreditNotificationEvent>()
            
            // Systems
            .add_systems(Startup, (
                load_credits,
                initialize_integration,
            ))
            .add_systems(Update, (
                handle_puzzle_completion,
                process_credit_transactions,
                sync_with_libertalia,
                update_credit_ui,
                show_credit_notifications,
            ).chain())
            .add_systems(OnExit(crate::GameState::InGame), save_credits);
    }
}

/// Event fired when credits are earned
#[derive(Event, Clone, Debug)]
pub struct CreditEarnedEvent {
    pub amount: u64,
    pub source: CreditSource,
    pub description: String,
    pub multipliers: Vec<RewardMultiplier>,
}

/// Event for credit synchronization with Libertalia
#[derive(Event, Clone, Debug)]
pub struct CreditSyncEvent {
    pub sync_type: SyncType,
    pub credits_synced: u64,
    pub success: bool,
    pub message: Option<String>,
}

#[derive(Clone, Debug)]
pub enum SyncType {
    Upload,
    Download,
    Verification,
}

/// Event for UI notifications about credits
#[derive(Event, Clone)]
pub struct CreditNotificationEvent {
    pub title: String,
    pub message: String,
    pub credit_amount: u64,
    pub notification_type: NotificationType,
}

#[derive(Clone, Debug)]
pub enum NotificationType {
    Earned,
    Milestone,
    Bonus,
    Sync,
}

/// Handle puzzle completion and award credits
fn handle_puzzle_completion(
    mut puzzle_events: EventReader<PuzzleSolvedEvent>,
    mut credits: ResMut<PapilioCredits>,
    calculator: Res<RewardCalculator>,
    mut credit_events: EventWriter<CreditEarnedEvent>,
    mut notification_events: EventWriter<CreditNotificationEvent>,
) {
    for event in puzzle_events.read() {
        // Calculate base reward based on puzzle difficulty
        let base_reward = calculator.calculate_base_reward(&event.puzzle_id);
        
        // Apply multipliers for performance
        let multipliers = calculator.calculate_multipliers(
            event.attempts,
            event.time_taken,
        );
        
        let total_reward = calculator.apply_multipliers(base_reward, &multipliers);
        
        // Add credits to player's balance
        let transaction = CreditTransaction {
            amount: total_reward,
            source: CreditSource::PuzzleSolved {
                puzzle_id: event.puzzle_id.clone(),
                difficulty: get_puzzle_difficulty(&event.puzzle_id),
                perfect_solve: event.attempts == 1,
            },
            timestamp: std::time::SystemTime::now(),
            synced: false,
        };
        
        credits.add_transaction(transaction.clone());
        
        // Fire events for UI and sync
        credit_events.send(CreditEarnedEvent {
            amount: total_reward,
            source: transaction.source.clone(),
            description: format!("Solved: {}", event.puzzle_id),
            multipliers: multipliers.clone(),
        });
        
        notification_events.send(CreditNotificationEvent {
            title: "Credits Earned!".to_string(),
            message: format!(
                "You earned {} Papilio credits for solving {}",
                total_reward, event.puzzle_id
            ),
            credit_amount: total_reward,
            notification_type: NotificationType::Earned,
        });
        
        // Check for milestones
        check_credit_milestones(&mut credits, &mut notification_events);
    }
}

/// Process pending credit transactions
fn process_credit_transactions(
    mut credits: ResMut<PapilioCredits>,
    time: Res<Time>,
) {
    credits.process_pending_transactions(time.delta_seconds());
}

/// Sync credits with Libertalia backend
fn sync_with_libertalia(
    mut credits: ResMut<PapilioCredits>,
    mut sync_status: ResMut<LibertaliaSyncStatus>,
    mut sync_events: EventWriter<CreditSyncEvent>,
    time: Res<Time>,
) {
    // Only sync periodically or when explicitly requested
    sync_status.update(time.delta_seconds());
    
    if sync_status.should_sync() {
        if let Some(unsynced) = credits.get_unsynced_transactions() {
            // Attempt to sync with Libertalia
            match integration::sync_transactions(&unsynced, &sync_status.api_config) {
                Ok(synced_count) => {
                    credits.mark_transactions_synced(synced_count);
                    sync_status.mark_successful_sync();
                    
                    sync_events.send(CreditSyncEvent {
                        sync_type: SyncType::Upload,
                        credits_synced: unsynced.iter().map(|t| t.amount).sum(),
                        success: true,
                        message: Some(format!("Synced {} transactions", synced_count)),
                    });
                }
                Err(err) => {
                    sync_status.mark_failed_sync();
                    
                    sync_events.send(CreditSyncEvent {
                        sync_type: SyncType::Upload,
                        credits_synced: 0,
                        success: false,
                        message: Some(format!("Sync failed: {}", err)),
                    });
                }
            }
        }
    }
}

/// Update credit display in UI
fn update_credit_ui(
    credits: Res<PapilioCredits>,
    mut query: Query<&mut Text, With<ui::CreditDisplay>>,
) {
    if credits.is_changed() {
        for mut text in &mut query {
            text.sections[0].value = format!("{} Papilio Credits", credits.total_balance());
        }
    }
}

/// Show credit notification popups
fn show_credit_notifications(
    mut commands: Commands,
    mut notification_events: EventReader<CreditNotificationEvent>,
    asset_server: Res<AssetServer>,
) {
    for event in notification_events.read() {
        ui::spawn_credit_notification(&mut commands, &asset_server, event.clone());
    }
}

/// Load credits from persistent storage
fn load_credits(mut credits: ResMut<PapilioCredits>) {
    if let Ok(saved_credits) = persistence::load_credits() {
        *credits = saved_credits;
        info!("Loaded {} Papilio credits from save", credits.total_balance());
    }
}

/// Save credits to persistent storage
fn save_credits(credits: Res<PapilioCredits>) {
    if let Err(e) = persistence::save_credits(&credits) {
        error!("Failed to save credits: {}", e);
    } else {
        info!("Saved {} Papilio credits", credits.total_balance());
    }
}

/// Initialize integration with Libertalia
fn initialize_integration(mut sync_status: ResMut<LibertaliaSyncStatus>) {
    sync_status.initialize();
}

/// Check if player reached any credit milestones
fn check_credit_milestones(
    credits: &mut PapilioCredits,
    notification_events: &mut EventWriter<CreditNotificationEvent>,
) {
    const MILESTONES: &[u64] = &[100, 500, 1000, 5000, 10000, 50000, 100000];
    
    let _balance = credits.total_balance();
    for &milestone in MILESTONES {
        if credits.just_passed_milestone(milestone) {
            notification_events.send(CreditNotificationEvent {
                title: "Milestone Reached!".to_string(),
                message: format!("You've earned {} total Papilio credits!", milestone),
                credit_amount: milestone,
                notification_type: NotificationType::Milestone,
            });
        }
    }
}

/// Helper function to get puzzle difficulty
fn get_puzzle_difficulty(puzzle_id: &str) -> Difficulty {
    // This would normally query the puzzle database
    // For now, return a default
    if puzzle_id.contains("tutorial") {
        Difficulty::Tutorial
    } else if puzzle_id.contains("easy") {
        Difficulty::Easy
    } else if puzzle_id.contains("hard") {
        Difficulty::Hard
    } else if puzzle_id.contains("expert") {
        Difficulty::Expert
    } else {
        Difficulty::Medium
    }
}