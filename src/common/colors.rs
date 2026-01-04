//! Unified color palette for the game's space theme.
//!
//! This module provides consistent colors across all UI modules,
//! ensuring a cohesive visual experience.

/// Deep space background colors
pub mod background {
    use bevy::prelude::Color;

    /// Primary background for menus and terminals
    pub const DEEP_SPACE: Color = Color::srgba(0.02, 0.0, 0.05, 0.98);

    /// Overlay for depth effects
    pub const OVERLAY: Color = Color::srgba(0.1, 0.0, 0.2, 0.3);

    /// Terminal-specific background
    pub const TERMINAL: Color = Color::srgba(0.08, 0.02, 0.15, 0.95);
}

/// Text colors for readability
pub mod text {
    use bevy::prelude::Color;

    /// Primary text - high contrast
    pub const PRIMARY: Color = Color::srgb(0.9, 0.85, 0.95);

    /// Secondary text - slightly dimmer
    pub const SECONDARY: Color = Color::srgb(0.7, 0.65, 0.8);

    /// Accent text for highlights
    pub const ACCENT: Color = Color::srgb(1.0, 0.6, 0.9);

    /// Title text - bright and prominent
    pub const TITLE: Color = Color::srgb(0.95, 0.75, 1.0);

    /// Glow effect for titles
    pub const TITLE_GLOW: Color = Color::srgba(0.8, 0.4, 1.0, 0.6);
}

/// Button state colors
pub mod button {
    use bevy::prelude::Color;

    /// Default button state
    pub const NORMAL: Color = Color::srgba(0.12, 0.04, 0.22, 0.75);

    /// Hovered button state
    pub const HOVER: Color = Color::srgba(0.25, 0.1, 0.45, 0.85);

    /// Selected/active button state
    pub const SELECTED: Color = Color::srgba(0.45, 0.2, 0.65, 0.95);

    /// Pressed button state
    pub const PRESSED: Color = Color::srgba(0.55, 0.25, 0.75, 1.0);
}

/// Terminal-specific colors
pub mod terminal {
    use bevy::prelude::Color;

    /// Terminal foreground text
    pub const FOREGROUND: Color = Color::srgb(0.85, 0.75, 0.95);

    /// Command prompt color
    pub const PROMPT: Color = Color::srgb(0.6, 0.3, 0.9);

    /// Error message color
    pub const ERROR: Color = Color::srgb(1.0, 0.3, 0.5);

    /// Success message color
    pub const SUCCESS: Color = Color::srgb(0.3, 0.95, 0.8);

    /// System message color
    pub const SYSTEM: Color = Color::srgb(0.5, 0.7, 1.0);

    /// Border glow effect
    pub const BORDER_GLOW: Color = Color::srgba(0.6, 0.2, 0.9, 0.8);
}

/// Effect colors for particles and visual elements
pub mod effects {
    use bevy::prelude::Color;

    /// Star/particle color
    pub const STAR: Color = Color::srgba(0.95, 0.9, 1.0, 0.8);

    /// Nebula cloud color
    pub const NEBULA: Color = Color::srgba(0.6, 0.2, 0.9, 0.03);

    /// Glow effect base color
    pub const GLOW: Color = Color::srgba(0.8, 0.3, 1.0, 0.3);
}

/// Settings/tab-specific colors
pub mod settings {
    use bevy::prelude::Color;

    /// Active tab background
    pub const TAB_ACTIVE: Color = Color::srgba(0.3, 0.1, 0.5, 0.9);

    /// Inactive tab background
    pub const TAB_INACTIVE: Color = Color::srgba(0.1, 0.05, 0.2, 0.7);

    /// Slider track color
    pub const SLIDER_TRACK: Color = Color::srgba(0.2, 0.1, 0.3, 0.8);

    /// Slider fill color
    pub const SLIDER_FILL: Color = Color::srgb(0.6, 0.3, 0.9);
}

/// Credits-specific colors
pub mod credits {
    use bevy::prelude::Color;

    /// Role/position text
    pub const ROLE: Color = Color::srgb(0.7, 0.5, 0.9);

    /// Name text
    pub const NAME: Color = Color::srgb(0.95, 0.9, 1.0);

    /// Section divider
    pub const SECTION: Color = Color::srgb(0.6, 0.8, 1.0);
}
