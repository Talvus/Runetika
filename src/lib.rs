// Library exports for testing and external use

// Core modules
pub mod terminal;
pub mod menu;
pub mod game_state;
pub mod credits;
pub mod settings;
pub mod spaceship;
pub mod spaceship_2d;
pub mod main_room;
pub mod maze;
pub mod player;
pub mod perspective;
pub mod puzzle;
pub mod silicon_mind;
pub mod terminal_interface;
pub mod terminal_commands;
pub mod creative_mechanics;

// Creative mechanics modules
pub mod glyph_resonance;
pub mod pattern_echo;
pub mod temporal_layers;
pub mod consciousness_fragments;
pub mod type_theory_viz;

// Debug modules (conditional compilation)
#[cfg(feature = "debug")]
pub mod type_theory_viz_debug;
#[cfg(feature = "debug")]
pub mod debug_overlay;
#[cfg(feature = "debug")]
pub mod type_inspector;