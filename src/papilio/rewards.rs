/// Reward calculation system for Papilio credits
/// 
/// This module handles the complex calculations for determining
/// how many credits a player earns based on their performance.

use bevy::prelude::*;
use serde::{Deserialize, Serialize};
use crate::arc_engine::Difficulty;

/// Calculator for determining credit rewards
#[derive(Resource, Clone, Debug, Serialize, Deserialize)]
pub struct RewardCalculator {
    /// Base rewards for each difficulty level
    base_rewards: BaseRewardTable,
    
    /// Multiplier configurations
    multiplier_config: MultiplierConfig,
    
    /// Special event multipliers (e.g., double credit weekends)
    event_multiplier: f32,
}

impl Default for RewardCalculator {
    fn default() -> Self {
        Self {
            base_rewards: BaseRewardTable::default(),
            multiplier_config: MultiplierConfig::default(),
            event_multiplier: 1.0,
        }
    }
}

impl RewardCalculator {
    /// Calculate base reward for a puzzle
    pub fn calculate_base_reward(&self, puzzle_id: &str) -> u64 {
        // In a real implementation, this would look up the specific puzzle
        // For now, use difficulty-based rewards
        let difficulty = self.infer_difficulty(puzzle_id);
        self.base_rewards.get_reward(difficulty)
    }
    
    /// Calculate performance multipliers
    pub fn calculate_multipliers(&self, attempts: u32, time_taken: f32) -> Vec<RewardMultiplier> {
        let mut multipliers = Vec::new();
        
        // Perfect solve bonus (first try)
        if attempts == 1 {
            multipliers.push(RewardMultiplier {
                name: "Perfect Solve".to_string(),
                value: self.multiplier_config.perfect_solve,
                multiplier_type: MultiplierType::Performance,
            });
        }
        
        // Speed bonus
        let speed_multiplier = self.calculate_speed_multiplier(time_taken);
        if speed_multiplier > 1.0 {
            multipliers.push(RewardMultiplier {
                name: "Speed Bonus".to_string(),
                value: speed_multiplier,
                multiplier_type: MultiplierType::Speed,
            });
        }
        
        // Efficiency bonus (low attempt count)
        if attempts <= 3 {
            let efficiency = 1.0 + (0.1 * (4 - attempts) as f32);
            multipliers.push(RewardMultiplier {
                name: "Efficiency Bonus".to_string(),
                value: efficiency,
                multiplier_type: MultiplierType::Efficiency,
            });
        }
        
        // Event multiplier
        if self.event_multiplier > 1.0 {
            multipliers.push(RewardMultiplier {
                name: "Special Event".to_string(),
                value: self.event_multiplier,
                multiplier_type: MultiplierType::Event,
            });
        }
        
        multipliers
    }
    
    /// Apply multipliers to base reward
    pub fn apply_multipliers(&self, base: u64, multipliers: &[RewardMultiplier]) -> u64 {
        let total_multiplier: f32 = multipliers.iter()
            .map(|m| m.value)
            .fold(1.0, |acc, val| acc * val);
        
        // Apply multipliers with ceiling to ensure players always get at least base reward
        ((base as f32 * total_multiplier).ceil() as u64).max(base)
    }
    
    /// Calculate speed-based multiplier
    fn calculate_speed_multiplier(&self, time_taken: f32) -> f32 {
        // Reward faster solutions
        // Under 30 seconds: up to 2x multiplier
        // 30-60 seconds: up to 1.5x multiplier
        // 60-120 seconds: up to 1.25x multiplier
        // Over 120 seconds: no speed bonus
        
        if time_taken < 30.0 {
            1.0 + (30.0 - time_taken) / 30.0
        } else if time_taken < 60.0 {
            1.0 + (60.0 - time_taken) / 60.0 * 0.5
        } else if time_taken < 120.0 {
            1.0 + (120.0 - time_taken) / 120.0 * 0.25
        } else {
            1.0
        }
    }
    
    /// Infer difficulty from puzzle ID
    fn infer_difficulty(&self, puzzle_id: &str) -> Difficulty {
        // This is a placeholder - in reality would query puzzle database
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
    
    /// Set event multiplier (for special events)
    pub fn set_event_multiplier(&mut self, multiplier: f32) {
        self.event_multiplier = multiplier.max(1.0);
    }
    
    /// Calculate bonus for pattern discovery
    pub fn calculate_pattern_discovery_reward(&self, novelty_score: f32, complexity: u32) -> u64 {
        // Base reward for pattern discovery
        let base = 50;
        
        // Novelty multiplier (1.0 to 3.0 based on how novel the pattern is)
        let novelty_mult = 1.0 + (novelty_score * 2.0);
        
        // Complexity multiplier (1.0 to 2.0 based on pattern complexity)
        let complexity_mult = 1.0 + (complexity.min(10) as f32 / 10.0);
        
        (base as f32 * novelty_mult * complexity_mult) as u64
    }
    
    /// Calculate bonus for proof completion
    pub fn calculate_proof_reward(&self, complexity: u32, correctness: f32) -> u64 {
        // Base reward for proofs
        let base = 100;
        
        // Complexity bonus (exponential growth)
        let complexity_mult = (1.5_f32).powi(complexity.min(10) as i32);
        
        // Correctness multiplier (partial credit for incomplete proofs)
        let correctness_mult = correctness;
        
        (base as f32 * complexity_mult * correctness_mult) as u64
    }
}

/// Table of base rewards by difficulty
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BaseRewardTable {
    tutorial: u64,
    easy: u64,
    medium: u64,
    hard: u64,
    expert: u64,
}

impl Default for BaseRewardTable {
    fn default() -> Self {
        Self {
            tutorial: 10,
            easy: 25,
            medium: 50,
            hard: 100,
            expert: 250,
        }
    }
}

impl BaseRewardTable {
    pub fn get_reward(&self, difficulty: Difficulty) -> u64 {
        match difficulty {
            Difficulty::Tutorial => self.tutorial,
            Difficulty::Easy => self.easy,
            Difficulty::Medium => self.medium,
            Difficulty::Hard => self.hard,
            Difficulty::Expert => self.expert,
        }
    }
}

/// Configuration for multipliers
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MultiplierConfig {
    pub perfect_solve: f32,
    pub max_speed_bonus: f32,
    pub max_efficiency_bonus: f32,
    pub streak_bonus_per_day: f32,
    pub max_streak_bonus: f32,
}

impl Default for MultiplierConfig {
    fn default() -> Self {
        Self {
            perfect_solve: 1.5,
            max_speed_bonus: 2.0,
            max_efficiency_bonus: 1.3,
            streak_bonus_per_day: 0.05,
            max_streak_bonus: 2.0,
        }
    }
}

/// Individual reward multiplier
#[derive(Clone, Debug)]
pub struct RewardMultiplier {
    pub name: String,
    pub value: f32,
    pub multiplier_type: MultiplierType,
}

#[derive(Clone, Debug)]
pub enum MultiplierType {
    Performance,
    Speed,
    Efficiency,
    Streak,
    Event,
    Bonus,
}