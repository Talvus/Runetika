/// Android Lifecycle Management
/// Handles Android activity lifecycle events

use std::sync::atomic::{AtomicI32, Ordering};
use crate::android::jni_bridge::JniError;

/// Android lifecycle states
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum LifecycleState {
    Created = 0,
    Started = 1,
    Resumed = 2,
    Paused = 3,
    Stopped = 4,
    Destroyed = 5,
}

impl From<i32> for LifecycleState {
    fn from(value: i32) -> Self {
        match value {
            0 => LifecycleState::Created,
            1 => LifecycleState::Started,
            2 => LifecycleState::Resumed,
            3 => LifecycleState::Paused,
            4 => LifecycleState::Stopped,
            5 => LifecycleState::Destroyed,
            _ => LifecycleState::Paused,
        }
    }
}

/// Current lifecycle state
static CURRENT_STATE: AtomicI32 = AtomicI32::new(LifecycleState::Created as i32);

/// Android lifecycle handler
pub struct AndroidLifecycle;

impl AndroidLifecycle {
    /// Handle lifecycle event from Android
    pub fn handle_event(event: i32) -> Result<(), JniError> {
        let state = LifecycleState::from(event);
        CURRENT_STATE.store(event, Ordering::SeqCst);

        match state {
            LifecycleState::Created => Self::on_create(),
            LifecycleState::Started => Self::on_start(),
            LifecycleState::Resumed => Self::on_resume(),
            LifecycleState::Paused => Self::on_pause(),
            LifecycleState::Stopped => Self::on_stop(),
            LifecycleState::Destroyed => Self::on_destroy(),
        }
    }

    /// Activity created
    fn on_create() -> Result<(), JniError> {
        // Initialize resources
        Ok(())
    }

    /// Activity started (visible)
    fn on_start() -> Result<(), JniError> {
        // Prepare for visibility
        Ok(())
    }

    /// Activity resumed (interactive)
    fn on_resume() -> Result<(), JniError> {
        // Resume game loop
        Ok(())
    }

    /// Activity paused (losing focus)
    fn on_pause() -> Result<(), JniError> {
        // Pause game loop
        Ok(())
    }

    /// Activity stopped (not visible)
    fn on_stop() -> Result<(), JniError> {
        // Save state
        Ok(())
    }

    /// Activity destroyed
    fn on_destroy() -> Result<(), JniError> {
        // Clean up resources
        Ok(())
    }

    /// Get current lifecycle state
    pub fn current_state() -> LifecycleState {
        LifecycleState::from(CURRENT_STATE.load(Ordering::SeqCst))
    }

    /// Check if app is active (resumed)
    pub fn is_active() -> bool {
        Self::current_state() == LifecycleState::Resumed
    }
}