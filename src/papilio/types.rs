/// Core types for the Papilio credit system
/// 
/// These types define the fundamental data structures for tracking,
/// earning, and managing credits within Runetika.

use bevy::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::VecDeque;
use std::time::SystemTime;
use crate::arc_engine::Difficulty;

/// Main resource tracking player's Papilio credits
#[derive(Resource, Default, Serialize, Deserialize, Clone, Debug)]
pub struct PapilioCredits {
    /// Current total balance
    balance: u64,
    
    /// Lifetime earnings (never decreases)
    lifetime_earned: u64,
    
    /// Transaction history
    transactions: VecDeque<CreditTransaction>,
    
    /// Pending transactions (not yet confirmed)
    pending: Vec<CreditTransaction>,
    
    /// Last milestone passed
    last_milestone: u64,
    
    /// Statistics
    stats: CreditStatistics,
}

impl PapilioCredits {
    /// Create new credit tracker with initial balance
    pub fn new(initial_balance: u64) -> Self {
        Self {
            balance: initial_balance,
            lifetime_earned: initial_balance,
            transactions: VecDeque::new(),
            pending: Vec::new(),
            last_milestone: 0,
            stats: CreditStatistics::default(),
        }
    }
    
    /// Get current balance
    pub fn total_balance(&self) -> u64 {
        self.balance
    }
    
    /// Get lifetime earnings
    pub fn lifetime_earnings(&self) -> u64 {
        self.lifetime_earned
    }
    
    /// Add a credit transaction
    pub fn add_transaction(&mut self, transaction: CreditTransaction) {
        self.balance += transaction.amount;
        self.lifetime_earned += transaction.amount;
        
        // Update statistics
        self.stats.update(&transaction);
        
        // Keep transaction history (max 1000 entries)
        self.transactions.push_front(transaction);
        if self.transactions.len() > 1000 {
            self.transactions.pop_back();
        }
    }
    
    /// Add pending transaction (awaiting confirmation)
    pub fn add_pending(&mut self, transaction: CreditTransaction) {
        self.pending.push(transaction);
    }
    
    /// Process pending transactions
    pub fn process_pending_transactions(&mut self, _delta: f32) {
        // Move confirmed transactions from pending to completed
        let mut i = 0;
        while i < self.pending.len() {
            if self.pending[i].is_confirmed() {
                let transaction = self.pending.remove(i);
                self.add_transaction(transaction);
            } else {
                i += 1;
            }
        }
    }
    
    /// Get unsynced transactions
    pub fn get_unsynced_transactions(&self) -> Option<Vec<CreditTransaction>> {
        let unsynced: Vec<_> = self.transactions
            .iter()
            .filter(|t| !t.synced)
            .cloned()
            .collect();
        
        if unsynced.is_empty() {
            None
        } else {
            Some(unsynced)
        }
    }
    
    /// Mark transactions as synced
    pub fn mark_transactions_synced(&mut self, count: usize) {
        let mut synced = 0;
        for transaction in &mut self.transactions {
            if !transaction.synced {
                transaction.synced = true;
                synced += 1;
                if synced >= count {
                    break;
                }
            }
        }
    }
    
    /// Check if just passed a milestone
    pub fn just_passed_milestone(&mut self, milestone: u64) -> bool {
        if self.balance >= milestone && self.last_milestone < milestone {
            self.last_milestone = milestone;
            true
        } else {
            false
        }
    }
    
    /// Get statistics
    pub fn statistics(&self) -> &CreditStatistics {
        &self.stats
    }
}

/// Individual credit transaction
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CreditTransaction {
    pub amount: u64,
    pub source: CreditSource,
    pub timestamp: SystemTime,
    pub synced: bool,
}

impl CreditTransaction {
    /// Check if transaction is confirmed (for pending transactions)
    pub fn is_confirmed(&self) -> bool {
        // In a real implementation, this would check with backend
        // For now, auto-confirm after creation
        true
    }
}

/// Source of credits
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum CreditSource {
    /// Credits from solving a puzzle
    PuzzleSolved {
        puzzle_id: String,
        difficulty: Difficulty,
        perfect_solve: bool,
    },
    
    /// Credits from discovering a pattern
    PatternDiscovered {
        pattern_type: String,
        novelty_score: f32,
    },
    
    /// Credits from completing a chapter/section
    ChapterComplete {
        chapter_id: String,
        completion_percentage: f32,
    },
    
    /// Credits from daily challenges
    DailyChallenge {
        challenge_id: String,
        rank: u32,
    },
    
    /// Credits from helping train AI
    AITrainingContribution {
        data_type: String,
        quality_score: f32,
    },
    
    /// Credits from mathematical proofs
    ProofCompleted {
        theorem_id: String,
        complexity: u32,
    },
    
    /// Bonus credits (events, achievements, etc.)
    Bonus {
        reason: String,
    },
    
    /// Initial grant or purchase
    Grant {
        source: String,
    },
}

/// Statistics about credit earnings
#[derive(Default, Clone, Debug, Serialize, Deserialize)]
pub struct CreditStatistics {
    pub puzzles_solved: u32,
    pub patterns_discovered: u32,
    pub perfect_solves: u32,
    pub chapters_completed: u32,
    pub daily_challenges_completed: u32,
    pub proofs_completed: u32,
    pub average_puzzle_reward: f32,
    pub highest_single_reward: u64,
    pub current_streak: u32,
    pub best_streak: u32,
    pub last_earn_time: Option<SystemTime>,
}

impl CreditStatistics {
    /// Update statistics based on a transaction
    pub fn update(&mut self, transaction: &CreditTransaction) {
        match &transaction.source {
            CreditSource::PuzzleSolved { perfect_solve, .. } => {
                self.puzzles_solved += 1;
                if *perfect_solve {
                    self.perfect_solves += 1;
                }
                
                // Update average
                let total = self.average_puzzle_reward * (self.puzzles_solved - 1) as f32;
                self.average_puzzle_reward = (total + transaction.amount as f32) / self.puzzles_solved as f32;
            }
            CreditSource::PatternDiscovered { .. } => {
                self.patterns_discovered += 1;
            }
            CreditSource::ChapterComplete { .. } => {
                self.chapters_completed += 1;
            }
            CreditSource::DailyChallenge { .. } => {
                self.daily_challenges_completed += 1;
            }
            CreditSource::ProofCompleted { .. } => {
                self.proofs_completed += 1;
            }
            _ => {}
        }
        
        // Update highest reward
        if transaction.amount > self.highest_single_reward {
            self.highest_single_reward = transaction.amount;
        }
        
        // Update streak
        if let Some(last_time) = self.last_earn_time {
            let elapsed = SystemTime::now()
                .duration_since(last_time)
                .unwrap_or_default();
            
            // If earned within 24 hours, continue streak
            if elapsed.as_secs() < 86400 {
                self.current_streak += 1;
                if self.current_streak > self.best_streak {
                    self.best_streak = self.current_streak;
                }
            } else {
                self.current_streak = 1;
            }
        } else {
            self.current_streak = 1;
        }
        
        self.last_earn_time = Some(SystemTime::now());
    }
}