/// Persistence layer for Papilio credits
/// 
/// Handles saving and loading credit data to/from disk,
/// ensuring players don't lose their hard-earned credits.

use bevy::prelude::*;
use std::fs;
use std::path::PathBuf;
use serde::{Deserialize, Serialize};
use crate::papilio::types::PapilioCredits;

/// Save credits to persistent storage
pub fn save_credits(credits: &PapilioCredits) -> Result<(), SaveError> {
    let path = get_credits_path();
    
    // Ensure directory exists
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| SaveError::IoError(e.to_string()))?;
    }
    
    // Serialize credits to JSON
    let json = serde_json::to_string_pretty(credits)
        .map_err(|e| SaveError::SerializationError(e.to_string()))?;
    
    // Write to file with atomic operation (write to temp, then rename)
    let temp_path = path.with_extension("tmp");
    fs::write(&temp_path, json).map_err(|e| SaveError::IoError(e.to_string()))?;
    fs::rename(temp_path, &path).map_err(|e| SaveError::IoError(e.to_string()))?;
    
    info!("Credits saved successfully to {:?}", path);
    Ok(())
}

/// Load credits from persistent storage
pub fn load_credits() -> Result<PapilioCredits, LoadError> {
    let path = get_credits_path();
    
    // Check if file exists
    if !path.exists() {
        info!("No existing credits file found, starting fresh");
        return Ok(PapilioCredits::default());
    }
    
    // Read file
    let json = fs::read_to_string(&path)
        .map_err(|e| LoadError::IoError(e.to_string()))?;
    
    // Deserialize
    let credits: PapilioCredits = serde_json::from_str(&json)
        .map_err(|e| LoadError::DeserializationError(e.to_string()))?;
    
    // Validate loaded data
    validate_credits(&credits)?;
    
    info!("Credits loaded successfully from {:?}", path);
    Ok(credits)
}

/// Get the platform-specific path for credits storage
fn get_credits_path() -> PathBuf {
    #[cfg(target_os = "macos")]
    {
        if let Some(home) = dirs::home_dir() {
            home.join("Library")
                .join("Application Support")
                .join("Runetika")
                .join("papilio_credits.json")
        } else {
            PathBuf::from("papilio_credits.json")
        }
    }
    
    #[cfg(target_os = "windows")]
    {
        if let Some(data_dir) = dirs::data_dir() {
            data_dir
                .join("Runetika")
                .join("papilio_credits.json")
        } else {
            PathBuf::from("papilio_credits.json")
        }
    }
    
    #[cfg(target_os = "linux")]
    {
        if let Some(config_dir) = dirs::config_dir() {
            config_dir
                .join("runetika")
                .join("papilio_credits.json")
        } else {
            PathBuf::from(".config/runetika/papilio_credits.json")
        }
    }
    
    #[cfg(target_arch = "wasm32")]
    {
        // For web builds, use browser local storage (not file system)
        PathBuf::from("papilio_credits.json")
    }
    
    #[cfg(not(any(target_os = "macos", target_os = "windows", target_os = "linux", target_arch = "wasm32")))]
    {
        PathBuf::from("papilio_credits.json")
    }
}

/// Validate loaded credits for integrity
fn validate_credits(credits: &PapilioCredits) -> Result<(), LoadError> {
    // Check that lifetime earnings >= current balance
    if credits.lifetime_earnings() < credits.total_balance() {
        return Err(LoadError::ValidationError(
            "Lifetime earnings less than current balance".to_string()
        ));
    }
    
    // Additional validation could be added here
    // - Check transaction timestamps are reasonable
    // - Verify cryptographic signatures if implemented
    // - Validate against known maximum values
    
    Ok(())
}

/// Create a backup of current credits
pub fn backup_credits(credits: &PapilioCredits) -> Result<(), SaveError> {
    let path = get_credits_path();
    let backup_path = path.with_extension("backup");
    
    // Save backup
    let json = serde_json::to_string_pretty(credits)
        .map_err(|e| SaveError::SerializationError(e.to_string()))?;
    fs::write(backup_path, json).map_err(|e| SaveError::IoError(e.to_string()))?;
    
    Ok(())
}

/// Restore credits from backup
pub fn restore_from_backup() -> Result<PapilioCredits, LoadError> {
    let path = get_credits_path();
    let backup_path = path.with_extension("backup");
    
    if !backup_path.exists() {
        return Err(LoadError::NoBackup);
    }
    
    let json = fs::read_to_string(&backup_path)
        .map_err(|e| LoadError::IoError(e.to_string()))?;
    
    let credits: PapilioCredits = serde_json::from_str(&json)
        .map_err(|e| LoadError::DeserializationError(e.to_string()))?;
    
    validate_credits(&credits)?;
    
    Ok(credits)
}

/// Export credits data for analysis or backup
pub fn export_credits(credits: &PapilioCredits, path: &PathBuf) -> Result<(), SaveError> {
    let export_data = CreditExport {
        credits: credits.clone(),
        export_time: std::time::SystemTime::now(),
        game_version: env!("CARGO_PKG_VERSION").to_string(),
    };
    
    let json = serde_json::to_string_pretty(&export_data)
        .map_err(|e| SaveError::SerializationError(e.to_string()))?;
    
    fs::write(path, json).map_err(|e| SaveError::IoError(e.to_string()))?;
    
    Ok(())
}

/// Import credits from export file
pub fn import_credits(path: &PathBuf) -> Result<PapilioCredits, LoadError> {
    let json = fs::read_to_string(path)
        .map_err(|e| LoadError::IoError(e.to_string()))?;
    
    let export_data: CreditExport = serde_json::from_str(&json)
        .map_err(|e| LoadError::DeserializationError(e.to_string()))?;
    
    validate_credits(&export_data.credits)?;
    
    Ok(export_data.credits)
}

/// Export format for credits
#[derive(Serialize, Deserialize)]
struct CreditExport {
    credits: PapilioCredits,
    export_time: std::time::SystemTime,
    game_version: String,
}

/// Save error types
#[derive(Debug)]
pub enum SaveError {
    IoError(String),
    SerializationError(String),
}

impl std::fmt::Display for SaveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IoError(msg) => write!(f, "IO error: {}", msg),
            Self::SerializationError(msg) => write!(f, "Serialization error: {}", msg),
        }
    }
}

impl std::error::Error for SaveError {}

/// Load error types
#[derive(Debug)]
pub enum LoadError {
    IoError(String),
    DeserializationError(String),
    ValidationError(String),
    NoBackup,
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IoError(msg) => write!(f, "IO error: {}", msg),
            Self::DeserializationError(msg) => write!(f, "Deserialization error: {}", msg),
            Self::ValidationError(msg) => write!(f, "Validation error: {}", msg),
            Self::NoBackup => write!(f, "No backup file found"),
        }
    }
}

impl std::error::Error for LoadError {}

// Web-specific persistence using browser local storage
#[cfg(target_arch = "wasm32")]
mod web_persistence {
    use super::*;
    use web_sys::Storage;
    
    const STORAGE_KEY: &str = "runetika_papilio_credits";
    
    /// Get browser local storage
    fn get_storage() -> Option<Storage> {
        web_sys::window()?
            .local_storage()
            .ok()?
    }
    
    /// Save credits to browser local storage
    pub fn save_to_local_storage(credits: &PapilioCredits) -> Result<(), SaveError> {
        let storage = get_storage()
            .ok_or_else(|| SaveError::IoError("Local storage not available".to_string()))?;
        
        let json = serde_json::to_string(credits)
            .map_err(|e| SaveError::SerializationError(e.to_string()))?;
        
        storage
            .set_item(STORAGE_KEY, &json)
            .map_err(|_| SaveError::IoError("Failed to write to local storage".to_string()))?;
        
        Ok(())
    }
    
    /// Load credits from browser local storage
    pub fn load_from_local_storage() -> Result<PapilioCredits, LoadError> {
        let storage = get_storage()
            .ok_or_else(|| LoadError::IoError("Local storage not available".to_string()))?;
        
        let json = storage
            .get_item(STORAGE_KEY)
            .map_err(|_| LoadError::IoError("Failed to read from local storage".to_string()))?
            .ok_or_else(|| LoadError::IoError("No saved credits found".to_string()))?;
        
        serde_json::from_str(&json)
            .map_err(|e| LoadError::DeserializationError(e.to_string()))
    }
}