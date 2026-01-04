//! Common utilities and shared components for the game.
//!
//! This module contains reusable code that is used across multiple
//! parts of the game, reducing duplication and ensuring consistency.

pub mod colors;
pub mod starfield;

// Re-export commonly used items
pub use starfield::{Particle, Star, StarfieldConfig, spawn_starfield_container, animate_particles};
