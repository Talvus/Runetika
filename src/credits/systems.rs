//! Systems for handling credits screen behavior and animations.
//!
//! This module contains all the update systems that control credits scrolling,
//! user input, and visual animations.

use bevy::prelude::*;
use crate::game_state::GameState;
use super::{CreditsState, CreditsContent, CreditEntry};

/// Handles user input while viewing credits.
///
/// # Input Handling
/// - `ESC`: Return to main menu
/// - `SPACE`: Toggle auto-scrolling
/// - `UP/DOWN`: Manual scroll control
/// - `HOME`: Jump to top
/// - `END`: Jump to bottom
pub fn handle_credits_input(
    keyboard: Res<ButtonInput<KeyCode>>,
    mut credits_state: ResMut<CreditsState>,
    mut next_state: ResMut<NextState<GameState>>,
) {
    // Return to menu
    if keyboard.just_pressed(KeyCode::Escape) {
        next_state.set(GameState::MainMenu);
    }
    
    // Toggle auto-scrolling
    if keyboard.just_pressed(KeyCode::Space) {
        credits_state.is_auto_scrolling = !credits_state.is_auto_scrolling;
    }
    
    // Manual scroll controls
    if keyboard.pressed(KeyCode::ArrowUp) {
        credits_state.scroll_position -= 200.0 * 0.016; // Assuming 60 FPS
        credits_state.is_auto_scrolling = false;
    }
    
    if keyboard.pressed(KeyCode::ArrowDown) {
        credits_state.scroll_position += 200.0 * 0.016;
        credits_state.is_auto_scrolling = false;
    }
    
    // Jump controls
    if keyboard.just_pressed(KeyCode::Home) {
        credits_state.scroll_position = 0.0;
        credits_state.is_auto_scrolling = false;
    }
    
    if keyboard.just_pressed(KeyCode::End) {
        credits_state.scroll_position = credits_state.content_height;
        credits_state.is_auto_scrolling = false;
    }
}

/// Animates the automatic scrolling of credits.
///
/// The credits will scroll automatically at a configured speed,
/// and loop back to the beginning when reaching the end.
pub fn animate_credits_scroll(
    time: Res<Time>,
    mut credits_state: ResMut<CreditsState>,
    mut content_query: Query<&mut Transform, With<CreditsContent>>,
) {
    if !credits_state.is_auto_scrolling {
        return;
    }
    
    // Update scroll position
    credits_state.scroll_position += credits_state.scroll_speed * time.delta_secs();
    
    // Loop back to start after showing all credits
    if credits_state.scroll_position > credits_state.content_height + 600.0 {
        credits_state.scroll_position = -100.0;
    }
    
    // Apply scroll to content
    for mut transform in content_query.iter_mut() {
        transform.translation.y = -credits_state.scroll_position;
    }
}

/// Animates individual credit entries with fade-in effects.
///
/// Each credit entry appears with a slight delay and fade-in animation
/// for a more polished presentation.
pub fn animate_credits_elements(
    time: Res<Time>,
    mut credit_entries: Query<(&mut CreditEntry, &mut TextColor, &Children)>,
    mut child_texts: Query<&mut TextColor, Without<CreditEntry>>,
) {
    for (mut entry, mut text_color, children) in credit_entries.iter_mut() {
        // Update animation timer
        entry.animation_timer += time.delta_secs();
        
        // Calculate alpha based on delay and animation progress
        let alpha = if entry.animation_timer > entry.delay {
            let progress = (entry.animation_timer - entry.delay).min(1.0);
            progress
        } else {
            0.0
        };
        
        // Apply alpha to main component
        text_color.0 = text_color.0.with_alpha(alpha);
        
        // Apply alpha to children
        for child in children.iter() {
            if let Ok(mut child_color) = child_texts.get_mut(child) {
                child_color.0 = child_color.0.with_alpha(alpha);
            }
        }
    }
}