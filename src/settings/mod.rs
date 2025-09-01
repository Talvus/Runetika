/// Settings module - Managing game configuration through layered abstractions
/// 
/// # Architecture Philosophy
/// This module demonstrates the principle of "Progressive Disclosure" - simple interfaces
/// that reveal complexity only when needed. Think of it like an iceberg: the visible API
/// is minimal, but the underlying systems are sophisticated.
///
/// # For Abstract Thinkers
/// The settings system operates as a hierarchical state machine where each configuration
/// domain (graphics, audio, controls) maintains its own invariants while participating
/// in a larger coherent system. Changes cascade through observers, maintaining consistency.
///
/// # For Concrete Thinkers  
/// This module handles all game settings like graphics quality, sound volume, and controls.
/// It saves settings to disk, loads them on startup, and applies them immediately when changed.

mod components;
mod systems;
mod ui;
mod persistence;

use bevy::prelude::*;
use crate::game_state::GameState;

pub use components::{SettingsData, GraphicsSettings, AudioSettings, ControlSettings};
pub use persistence::SettingsFile;

/// Plugin that manages all settings-related functionality
/// 
/// # Conceptual Model
/// Settings flow through three layers:
/// 1. **Presentation Layer** (UI) - User-facing controls
/// 2. **Domain Layer** (SettingsData) - Business logic and validation  
/// 3. **Persistence Layer** (SettingsFile) - Storage and retrieval
pub struct SettingsPlugin;

impl Plugin for SettingsPlugin {
    fn build(&self, app: &mut App) {
        app
            // Resources represent global state
            .init_resource::<SettingsData>()
            .init_resource::<SettingsFile>()
            
            // State transitions define the settings lifecycle
            .add_systems(OnEnter(GameState::Settings), (
                ui::setup_settings_screen,
                systems::load_settings_from_disk,
            ))
            .add_systems(OnExit(GameState::Settings), (
                ui::cleanup_settings_screen,
                systems::save_settings_to_disk,
            ))
            
            // Runtime systems handle continuous updates
            .add_systems(Update, (
                systems::handle_settings_input,
                systems::apply_graphics_changes,
                systems::apply_audio_changes,
                systems::update_settings_display,
            ).run_if(in_state(GameState::Settings)))
            
            // Platform-specific optimizations
            .add_systems(Startup, systems::detect_platform_capabilities);
    }
}

/// High-level settings API for external modules
/// 
/// # Design Pattern: Facade
/// This provides a simplified interface to the complex settings subsystem.
/// Other modules don't need to understand the internal structure.
impl SettingsData {
    /// Apply all settings to the game engine
    /// 
    /// # Abstract View
    /// This method acts as a synchronization point where the abstract configuration
    /// space maps onto the concrete engine state space.
    /// 
    /// # Practical View
    /// This updates the game with the current settings - changes resolution,
    /// adjusts volume, remaps controls, etc.
    pub fn apply_all(&self, 
        windows: &mut Query<&mut Window>,
        commands: &mut Commands,
    ) {
        self.graphics.apply_to_window(windows);
        self.audio.apply_to_audio_system();
        self.controls.apply_to_input_system(commands);
    }
    
    /// Get optimal settings for the current platform
    /// 
    /// # Abstraction
    /// This embodies the concept of "context-aware configuration" - settings that
    /// adapt to their environment rather than being fixed.
    #[cfg(target_os = "macos")]
    pub fn platform_optimal() -> Self {
        Self {
            graphics: GraphicsSettings::apple_silicon_optimal(),
            audio: AudioSettings::default(),
            controls: ControlSettings::default(),
        }
    }
    
    #[cfg(not(target_os = "macos"))]
    pub fn platform_optimal() -> Self {
        Self::default()
    }
}