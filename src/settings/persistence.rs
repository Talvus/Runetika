/// Settings persistence - Saving and loading configuration
/// 
/// # Persistence Philosophy
/// Settings should persist across game sessions but remain human-readable
/// for debugging and manual editing. JSON provides this balance.

use bevy::prelude::*;
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::PathBuf;
use super::SettingsData;

/// Settings file manager
/// 
/// # File Location Strategy
/// Uses platform-specific directories for proper OS integration:
/// - Respects user expectations for config file locations
/// - Allows cloud sync on platforms that support it
/// - Ensures proper permissions and accessibility
#[derive(Resource)]
pub struct SettingsFile {
    path: PathBuf,
}

impl Default for SettingsFile {
    fn default() -> Self {
        Self {
            path: Self::get_settings_path(),
        }
    }
}

impl SettingsFile {
    /// Get the platform-specific settings file path
    /// 
    /// # Cross-Platform Considerations
    /// Each OS has conventions for where config files should live.
    /// We respect these to be a good citizen on each platform.
    fn get_settings_path() -> PathBuf {
        #[cfg(target_os = "macos")]
        {
            // macOS: ~/Library/Application Support/Runetika/settings.json
            if let Some(home) = dirs::home_dir() {
                home.join("Library")
                    .join("Application Support")
                    .join("Runetika")
                    .join("settings.json")
            } else {
                PathBuf::from("settings.json")
            }
        }
        
        #[cfg(target_os = "linux")]
        {
            // Linux: ~/.config/runetika/settings.json
            if let Some(config) = dirs::config_dir() {
                config.join("runetika").join("settings.json")
            } else {
                PathBuf::from("settings.json")
            }
        }
        
        #[cfg(target_os = "windows")]
        {
            // Windows: %APPDATA%/Runetika/settings.json
            if let Some(data) = dirs::data_dir() {
                data.join("Runetika").join("settings.json")
            } else {
                PathBuf::from("settings.json")
            }
        }
        
        #[cfg(not(any(target_os = "macos", target_os = "linux", target_os = "windows")))]
        {
            // Fallback for other platforms
            PathBuf::from("settings.json")
        }
    }
    
    /// Load settings from disk
    /// 
    /// # Error Handling
    /// Returns Ok with loaded settings or Err if:
    /// - File doesn't exist (first run)
    /// - File is corrupted
    /// - Permissions issue
    pub fn load(&self) -> Result<SettingsData, String> {
        // Read file
        let contents = fs::read_to_string(&self.path)
            .map_err(|e| format!("Could not read settings file: {}", e))?;
        
        // Parse JSON
        let settings: SettingsData = serde_json::from_str(&contents)
            .map_err(|e| format!("Could not parse settings: {}", e))?;
        
        Ok(settings)
    }
    
    /// Save settings to disk
    /// 
    /// # Atomic Writes
    /// In production, we'd write to a temp file first,
    /// then rename it to ensure atomic updates.
    pub fn save(&mut self, settings: &SettingsData) -> Result<(), String> {
        // Ensure directory exists
        if let Some(parent) = self.path.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| format!("Could not create settings directory: {}", e))?;
        }
        
        // Serialize to pretty JSON for human readability
        let json = serde_json::to_string_pretty(settings)
            .map_err(|e| format!("Could not serialize settings: {}", e))?;
        
        // Write to file
        fs::write(&self.path, json)
            .map_err(|e| format!("Could not write settings file: {}", e))?;
        
        Ok(())
    }
    
    /// Reset settings to defaults
    /// 
    /// # Use Cases
    /// - User wants to start fresh
    /// - Settings corrupted
    /// - Major version upgrade
    pub fn reset(&mut self) -> Result<(), String> {
        self.save(&SettingsData::default())
    }
    
    /// Check if settings file exists
    pub fn exists(&self) -> bool {
        self.path.exists()
    }
}