/// Integration layer for Papilio/Libertalia backend
/// 
/// This module handles the communication with the external Libertalia
/// platform for credit synchronization and validation.

use bevy::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use crate::papilio::types::CreditTransaction;

/// Status and configuration for Libertalia sync
#[derive(Resource, Default, Clone, Debug)]
pub struct LibertaliaSyncStatus {
    pub api_config: APIConfig,
    pub is_connected: bool,
    pub last_sync_time: f64,
    pub sync_interval: f64,
    pub pending_sync: bool,
    pub sync_failures: u32,
    pub total_syncs: u32,
}

impl LibertaliaSyncStatus {
    /// Initialize the integration
    pub fn initialize(&mut self) {
        self.api_config = APIConfig::from_env();
        self.sync_interval = 60.0; // Sync every 60 seconds
        self.is_connected = self.test_connection();
        
        if self.is_connected {
            info!("Connected to Libertalia credit system");
        } else {
            warn!("Could not connect to Libertalia - credits will be stored locally");
        }
    }
    
    /// Update sync timer
    pub fn update(&mut self, delta: f32) {
        self.last_sync_time += delta as f64;
    }
    
    /// Check if it's time to sync
    pub fn should_sync(&self) -> bool {
        self.is_connected 
            && self.last_sync_time >= self.sync_interval 
            && self.sync_failures < 5 // Stop trying after 5 failures
    }
    
    /// Mark successful sync
    pub fn mark_successful_sync(&mut self) {
        self.last_sync_time = 0.0;
        self.sync_failures = 0;
        self.total_syncs += 1;
        self.pending_sync = false;
    }
    
    /// Mark failed sync
    pub fn mark_failed_sync(&mut self) {
        self.sync_failures += 1;
        self.pending_sync = true;
        
        // Exponential backoff on failures
        self.sync_interval = (60.0 * (2_f64).powi(self.sync_failures as i32)).min(3600.0);
    }
    
    /// Test connection to Libertalia
    fn test_connection(&self) -> bool {
        // In production, this would actually ping the API
        // For now, check if configuration exists
        !self.api_config.endpoint.is_empty()
    }
}

/// API configuration for Libertalia
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct APIConfig {
    pub endpoint: String,
    pub api_key: String,
    pub player_id: String,
    pub environment: Environment,
}

impl APIConfig {
    /// Load configuration from environment or config file
    pub fn from_env() -> Self {
        // In production, load from environment variables or secure storage
        // For development, use mock configuration
        Self {
            endpoint: std::env::var("LIBERTALIA_ENDPOINT")
                .unwrap_or_else(|_| "https://api.libertalia.example/v1".to_string()),
            api_key: std::env::var("LIBERTALIA_API_KEY")
                .unwrap_or_else(|_| "dev-key-placeholder".to_string()),
            player_id: std::env::var("LIBERTALIA_PLAYER_ID")
                .unwrap_or_else(|_| generate_player_id()),
            environment: Environment::Development,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Environment {
    Production,
    Staging,
    Development,
}

impl Default for Environment {
    fn default() -> Self {
        Self::Development
    }
}

/// Sync transactions with Libertalia backend
pub fn sync_transactions(
    transactions: &[CreditTransaction],
    config: &APIConfig,
) -> Result<usize, SyncError> {
    // In production, this would make actual API calls
    // For now, simulate the sync process
    
    if config.environment == Environment::Development {
        // Simulate successful sync in development
        return Ok(transactions.len());
    }
    
    // Convert transactions to API format
    let api_transactions: Vec<APITransaction> = transactions
        .iter()
        .map(|t| APITransaction::from(t.clone()))
        .collect();
    
    // Simulate API call
    match send_to_libertalia(&api_transactions, config) {
        Ok(response) => {
            info!("Synced {} transactions to Libertalia", response.synced_count);
            Ok(response.synced_count)
        }
        Err(e) => {
            error!("Failed to sync with Libertalia: {:?}", e);
            Err(e)
        }
    }
}

/// Send transactions to Libertalia API
fn send_to_libertalia(
    transactions: &[APITransaction],
    config: &APIConfig,
) -> Result<SyncResponse, SyncError> {
    // This would be replaced with actual HTTP client call
    // For now, return mock response
    
    if config.api_key == "dev-key-placeholder" {
        // Development mode - always succeed
        return Ok(SyncResponse {
            synced_count: transactions.len(),
            total_credits: transactions.iter().map(|t| t.amount).sum(),
            new_balance: 0, // Would be returned by API
            message: "Development mode sync".to_string(),
        });
    }
    
    // Simulate network conditions
    if rand::random::<f32>() > 0.95 {
        return Err(SyncError::NetworkError("Simulated network failure".to_string()));
    }
    
    Ok(SyncResponse {
        synced_count: transactions.len(),
        total_credits: transactions.iter().map(|t| t.amount).sum(),
        new_balance: 0,
        message: "Success".to_string(),
    })
}

/// Verify credit balance with backend
pub fn verify_balance(config: &APIConfig) -> Result<u64, SyncError> {
    // In production, query the actual balance from Libertalia
    // For now, return a mock value
    
    if config.environment == Environment::Development {
        return Ok(0);
    }
    
    // Simulate API call
    Ok(0)
}

/// Transaction format for API
#[derive(Clone, Debug, Serialize, Deserialize)]
struct APITransaction {
    pub amount: u64,
    pub source_type: String,
    pub source_details: HashMap<String, String>,
    pub timestamp: i64,
    pub player_id: String,
    pub game_version: String,
}

impl From<CreditTransaction> for APITransaction {
    fn from(transaction: CreditTransaction) -> Self {
        let mut details = HashMap::new();
        let source_type = match &transaction.source {
            crate::papilio::CreditSource::PuzzleSolved { puzzle_id, difficulty, perfect_solve } => {
                details.insert("puzzle_id".to_string(), puzzle_id.clone());
                details.insert("difficulty".to_string(), format!("{:?}", difficulty));
                details.insert("perfect_solve".to_string(), perfect_solve.to_string());
                "puzzle_solved"
            }
            crate::papilio::CreditSource::PatternDiscovered { pattern_type, novelty_score } => {
                details.insert("pattern_type".to_string(), pattern_type.clone());
                details.insert("novelty_score".to_string(), novelty_score.to_string());
                "pattern_discovered"
            }
            crate::papilio::CreditSource::ChapterComplete { chapter_id, completion_percentage } => {
                details.insert("chapter_id".to_string(), chapter_id.clone());
                details.insert("completion".to_string(), completion_percentage.to_string());
                "chapter_complete"
            }
            _ => "other"
        }.to_string();
        
        Self {
            amount: transaction.amount,
            source_type,
            source_details: details,
            timestamp: transaction.timestamp
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs() as i64,
            player_id: String::new(), // Will be filled by API config
            game_version: env!("CARGO_PKG_VERSION").to_string(),
        }
    }
}

/// Response from sync operation
#[derive(Debug, Deserialize)]
struct SyncResponse {
    pub synced_count: usize,
    pub total_credits: u64,
    pub new_balance: u64,
    pub message: String,
}

/// Sync error types
#[derive(Debug)]
pub enum SyncError {
    NetworkError(String),
    AuthenticationError(String),
    ValidationError(String),
    ServerError(String),
    Unknown(String),
}

impl std::fmt::Display for SyncError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NetworkError(msg) => write!(f, "Network error: {}", msg),
            Self::AuthenticationError(msg) => write!(f, "Authentication failed: {}", msg),
            Self::ValidationError(msg) => write!(f, "Validation error: {}", msg),
            Self::ServerError(msg) => write!(f, "Server error: {}", msg),
            Self::Unknown(msg) => write!(f, "Unknown error: {}", msg),
        }
    }
}

impl std::error::Error for SyncError {}

/// Generate a unique player ID for development
fn generate_player_id() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis();
    
    format!("dev_player_{}", timestamp)
}

/// Integration hooks for external systems
pub trait PapilioIntegration {
    /// Called when credits are earned
    fn on_credits_earned(&self, amount: u64, source: &str);
    
    /// Called when credits are spent (future feature)
    fn on_credits_spent(&self, amount: u64, item: &str);
    
    /// Called when sync completes
    fn on_sync_complete(&self, success: bool, synced: u64);
    
    /// Get current exchange rate (if applicable)
    fn get_exchange_rate(&self) -> f32;
}

/// Default implementation for development
pub struct DefaultIntegration;

impl PapilioIntegration for DefaultIntegration {
    fn on_credits_earned(&self, amount: u64, source: &str) {
        debug!("Credits earned: {} from {}", amount, source);
    }
    
    fn on_credits_spent(&self, amount: u64, item: &str) {
        debug!("Credits spent: {} on {}", amount, item);
    }
    
    fn on_sync_complete(&self, success: bool, synced: u64) {
        debug!("Sync complete: success={}, synced={}", success, synced);
    }
    
    fn get_exchange_rate(&self) -> f32 {
        1.0 // 1:1 exchange rate in development
    }
}