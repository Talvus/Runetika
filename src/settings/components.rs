/// Component definitions for the settings system
/// 
/// # Design Philosophy: Algebraic Data Types
/// Each settings structure forms an algebraic type that can be composed and transformed.
/// Think of these as mathematical objects with well-defined operations.

use bevy::prelude::*;
use serde::{Deserialize, Serialize};

/// Root settings container - the sum of all configuration domains
/// 
/// # Abstract Interpretation
/// This is a product type combining orthogonal configuration spaces.
/// Each field represents an independent dimension of customization.
/// 
/// # Concrete Usage
/// This struct holds all the game's settings in one place.
#[derive(Resource, Debug, Clone, Serialize, Deserialize)]
pub struct SettingsData {
    pub graphics: GraphicsSettings,
    pub audio: AudioSettings,
    pub controls: ControlSettings,
    pub gameplay: GameplaySettings,
}

impl Default for SettingsData {
    fn default() -> Self {
        Self {
            graphics: GraphicsSettings::default(),
            audio: AudioSettings::default(),
            controls: ControlSettings::default(),
            gameplay: GameplaySettings::default(),
        }
    }
}

/// Graphics configuration space
/// 
/// # Conceptual Model
/// Graphics settings form a multi-dimensional optimization problem:
/// - Quality vs Performance
/// - Resolution vs Framerate  
/// - Effects vs Stability
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GraphicsSettings {
    /// Resolution scale factor (0.5 = half res, 2.0 = double res)
    /// Abstract: Sampling density in screen space
    /// Concrete: Makes the game sharper or blurrier
    pub resolution_scale: f32,
    
    /// Vertical sync mode
    /// Abstract: Temporal synchronization strategy
    /// Concrete: Prevents screen tearing
    pub vsync: VSyncMode,
    
    /// Shadow quality level (0 = off, 3 = ultra)
    /// Abstract: Photon simulation fidelity
    /// Concrete: How good shadows look
    pub shadow_quality: u8,
    
    /// Anti-aliasing mode
    /// Abstract: Spatial frequency filtering
    /// Concrete: Smooths jagged edges
    pub antialiasing: AAMode,
    
    /// Particle density multiplier
    /// Abstract: Statistical sampling rate for effects
    /// Concrete: How many particles appear
    pub particle_density: f32,
    
    /// Target frames per second (0 = unlimited)
    pub target_fps: u32,
}

impl GraphicsSettings {
    /// Optimal settings for Apple Silicon
    /// Leverages Metal API and unified memory architecture
    #[cfg(target_os = "macos")]
    pub fn apple_silicon_optimal() -> Self {
        Self {
            resolution_scale: 1.0,  // Native resolution performs best
            vsync: VSyncMode::Adaptive,  // ProMotion support
            shadow_quality: 2,  // Medium - good balance
            antialiasing: AAMode::TAA,  // Temporal AA works well with Metal
            particle_density: 1.0,
            target_fps: 120,  // ProMotion displays
        }
    }
    
    pub fn apply_to_window(&self, windows: &mut Query<&mut Window>) {
        // Implementation would apply these settings
    }
}

impl Default for GraphicsSettings {
    fn default() -> Self {
        Self {
            resolution_scale: 1.0,
            vsync: VSyncMode::On,
            shadow_quality: 1,
            antialiasing: AAMode::FXAA,
            particle_density: 1.0,
            target_fps: 60,
        }
    }
}

/// V-Sync modes with platform considerations
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq)]
pub enum VSyncMode {
    Off,       // No synchronization
    On,        // Traditional VSync
    Adaptive,  // Smart VSync (great for Apple ProMotion)
    Fast,      // Triple buffering
}

/// Anti-aliasing techniques
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq)]
pub enum AAMode {
    Off,
    FXAA,  // Fast Approximate AA
    TAA,   // Temporal AA
    MSAA2x,  // Multi-Sample AA
    MSAA4x,
    MSAA8x,
}

/// Audio configuration
/// 
/// # Abstract Model
/// Audio settings define a perceptual space mapping decibels to subjective loudness
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AudioSettings {
    /// Master volume (0.0 - 1.0)
    /// Logarithmic scale for perceptual linearity
    pub master_volume: f32,
    
    /// Category-specific volumes
    pub music_volume: f32,
    pub sfx_volume: f32,
    pub ambient_volume: f32,
    pub ui_volume: f32,
    
    /// Spatial audio settings
    pub spatial_audio: bool,
    pub audio_device: Option<String>,
}

impl AudioSettings {
    pub fn apply_to_audio_system(&self, _audio: &bevy::audio::Audio) {
        // Would apply volume settings here
    }
}

impl Default for AudioSettings {
    fn default() -> Self {
        Self {
            master_volume: 0.7,
            music_volume: 0.8,
            sfx_volume: 1.0,
            ambient_volume: 0.6,
            ui_volume: 0.9,
            spatial_audio: true,
            audio_device: None,
        }
    }
}

/// Control configuration
/// 
/// # Design Pattern: Command Pattern
/// Controls map inputs to abstract commands, decoupling physical keys from game actions
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ControlSettings {
    pub mouse_sensitivity: f32,
    pub invert_y_axis: bool,
    pub key_bindings: KeyBindings,
}

impl ControlSettings {
    pub fn apply_to_input_system(&self, _commands: &mut Commands) {
        // Would reconfigure input mappings here
    }
}

impl Default for ControlSettings {
    fn default() -> Self {
        Self {
            mouse_sensitivity: 1.0,
            invert_y_axis: false,
            key_bindings: KeyBindings::default(),
        }
    }
}

/// Key binding configuration
/// Note: We use String instead of KeyCode for serialization compatibility
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KeyBindings {
    pub up: String,
    pub down: String,
    pub left: String,
    pub right: String,
    pub interact: String,
    pub terminal: String,
    pub pause: String,
}

impl Default for KeyBindings {
    fn default() -> Self {
        Self {
            up: "W".to_string(),
            down: "S".to_string(),
            left: "A".to_string(),
            right: "D".to_string(),
            interact: "E".to_string(),
            terminal: "Backquote".to_string(),
            pause: "Escape".to_string(),
        }
    }
}

impl KeyBindings {
    /// Convert string key names to Bevy KeyCodes
    pub fn get_keycode(&self, key_name: &str) -> Option<KeyCode> {
        match key_name {
            "W" => Some(KeyCode::KeyW),
            "S" => Some(KeyCode::KeyS),
            "A" => Some(KeyCode::KeyA),
            "D" => Some(KeyCode::KeyD),
            "E" => Some(KeyCode::KeyE),
            "Backquote" => Some(KeyCode::Backquote),
            "Escape" => Some(KeyCode::Escape),
            _ => None,
        }
    }
}

/// Gameplay settings
/// 
/// # Abstract Perspective
/// These settings define the game's difficulty manifold - a continuous space
/// where each point represents a different challenge configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GameplaySettings {
    pub difficulty: Difficulty,
    pub auto_save: bool,
    pub save_interval_minutes: u32,
    pub show_hints: bool,
    pub tutorial_enabled: bool,
}

impl Default for GameplaySettings {
    fn default() -> Self {
        Self {
            difficulty: Difficulty::Normal,
            auto_save: true,
            save_interval_minutes: 5,
            show_hints: true,
            tutorial_enabled: true,
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq)]
pub enum Difficulty {
    Casual,    // For story and exploration
    Normal,    // Balanced challenge
    Hard,      // For experienced players
    Nightmare, // Maximum challenge
    Custom,    // Player-defined parameters
}

/// UI marker components
#[derive(Component)]
pub struct SettingsScreen;

#[derive(Component)]
pub struct SettingsTab {
    pub tab_type: SettingsTabType,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SettingsTabType {
    Graphics,
    Audio,
    Controls,
    Gameplay,
}