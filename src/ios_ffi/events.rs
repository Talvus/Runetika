/// Event System for iOS → Bevy Communication
/// 
/// This module provides thread-safe event passing from iOS to the Bevy engine.

use super::*;
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};
use parking_lot::RwLock;

/// Thread-safe event bus for iOS events
pub struct EventBus {
    /// Pending events to be processed
    events: Arc<Mutex<VecDeque<IOSEvent>>>,
    /// Event handlers registered by Bevy systems
    handlers: Arc<RwLock<Vec<Box<dyn EventHandler>>>>,
    /// Maximum queue size to prevent memory issues
    max_queue_size: usize,
}

impl EventBus {
    /// Create a new event bus
    pub fn new(max_queue_size: usize) -> Self {
        Self {
            events: Arc::new(Mutex::new(VecDeque::with_capacity(max_queue_size))),
            handlers: Arc::new(RwLock::new(Vec::new())),
            max_queue_size,
        }
    }
    
    /// Push an event to the queue
    pub fn push_event(&self, event: IOSEvent) -> Result<(), String> {
        let mut queue = self.events.lock().map_err(|_| "Failed to lock event queue")?;
        
        // Check queue size
        if queue.len() >= self.max_queue_size {
            // Remove oldest event if queue is full
            queue.pop_front();
        }
        
        queue.push_back(event);
        Ok(())
    }
    
    /// Process all pending events
    pub fn process_events(&self) {
        let events: Vec<IOSEvent> = {
            let mut queue = match self.events.lock() {
                Ok(q) => q,
                Err(_) => return,
            };
            queue.drain(..).collect()
        };
        
        let handlers = self.handlers.read();
        for event in events {
            for handler in handlers.iter() {
                handler.handle_event(&event);
            }
        }
    }
    
    /// Register an event handler
    pub fn register_handler(&self, handler: Box<dyn EventHandler>) {
        let mut handlers = self.handlers.write();
        handlers.push(handler);
    }
}

/// Trait for event handlers
pub trait EventHandler: Send + Sync {
    /// Handle an iOS event
    fn handle_event(&self, event: &IOSEvent);
}

/// Send a custom event with arbitrary data
///
/// # Safety
/// The data pointer must be valid and the size must be correct.
#[no_mangle]
pub unsafe extern "C" fn runetika_send_custom_event(
    handle: *mut EngineHandle,
    event_id: u32,
    data: *const u8,
    data_size: usize,
) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }
    
    if data.is_null() && data_size > 0 {
        return ERROR_INVALID_PARAMETER;
    }
    
    let handle = &*handle;
    
    // Copy data into a Vec
    let event_data = if data_size > 0 {
        std::slice::from_raw_parts(data, data_size).to_vec()
    } else {
        Vec::new()
    };
    
    let event = IOSEvent::Custom(event_id, event_data);
    
    match handle.event_queue.lock() {
        Ok(mut queue) => {
            queue.push(event);
            SUCCESS
        }
        Err(_) => ERROR_LOCK_FAILED,
    }
}

/// Send a lifecycle event
///
/// # Safety
/// The handle must be valid.
#[no_mangle]
pub unsafe extern "C" fn runetika_send_lifecycle_event(
    handle: *mut EngineHandle,
    event: u32,
) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }
    
    let handle = &*handle;
    
    let lifecycle_event = match event {
        0 => LifecycleEvent::WillEnterForeground,
        1 => LifecycleEvent::DidBecomeActive,
        2 => LifecycleEvent::WillResignActive,
        3 => LifecycleEvent::DidEnterBackground,
        4 => LifecycleEvent::WillTerminate,
        5 => LifecycleEvent::MemoryWarning,
        _ => return ERROR_INVALID_PARAMETER,
    };
    
    let event = IOSEvent::Lifecycle(lifecycle_event);
    
    match handle.event_queue.lock() {
        Ok(mut queue) => {
            queue.push(event);
            SUCCESS
        }
        Err(_) => ERROR_LOCK_FAILED,
    }
}

/// Send a device orientation change event
///
/// # Safety
/// The handle must be valid.
#[no_mangle]
pub unsafe extern "C" fn runetika_send_orientation_event(
    handle: *mut EngineHandle,
    orientation: u32,
) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }
    
    let handle = &*handle;
    
    let device_orientation = match orientation {
        0 => DeviceOrientation::Unknown,
        1 => DeviceOrientation::Portrait,
        2 => DeviceOrientation::PortraitUpsideDown,
        3 => DeviceOrientation::LandscapeLeft,
        4 => DeviceOrientation::LandscapeRight,
        5 => DeviceOrientation::FaceUp,
        6 => DeviceOrientation::FaceDown,
        _ => return ERROR_INVALID_PARAMETER,
    };
    
    let event = IOSEvent::Orientation(device_orientation);
    
    match handle.event_queue.lock() {
        Ok(mut queue) => {
            queue.push(event);
            SUCCESS
        }
        Err(_) => ERROR_LOCK_FAILED,
    }
}

/// Send gyroscope data
///
/// # Safety
/// The handle must be valid.
#[no_mangle]
pub unsafe extern "C" fn runetika_send_gyroscope(
    handle: *mut EngineHandle,
    x: f32,
    y: f32,
    z: f32,
) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }
    
    let handle = &*handle;
    
    let event = IOSEvent::Gyroscope(GyroscopeEvent {
        rotation_rate: (x, y, z),
        timestamp: std::time::SystemTime::now(),
    });
    
    match handle.event_queue.lock() {
        Ok(mut queue) => {
            queue.push(event);
            SUCCESS
        }
        Err(_) => ERROR_LOCK_FAILED,
    }
}

/// Batch send multiple touch events for better performance
///
/// # Safety
/// The handle and touches pointer must be valid.
#[no_mangle]
pub unsafe extern "C" fn runetika_send_touches_batch(
    handle: *mut EngineHandle,
    touches: *const TouchEvent,
    count: usize,
) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }
    
    if touches.is_null() && count > 0 {
        return ERROR_INVALID_PARAMETER;
    }
    
    let handle = &*handle;
    
    // Convert raw touches to events
    let touch_events: Vec<IOSEvent> = if count > 0 {
        std::slice::from_raw_parts(touches, count)
            .iter()
            .map(|t| IOSEvent::Touch(t.clone()))
            .collect()
    } else {
        Vec::new()
    };
    
    match handle.event_queue.lock() {
        Ok(mut queue) => {
            queue.extend(touch_events);
            SUCCESS
        }
        Err(_) => ERROR_LOCK_FAILED,
    }
}

/// Clear all pending events
///
/// # Safety
/// The handle must be valid.
#[no_mangle]
pub unsafe extern "C" fn runetika_clear_events(handle: *mut EngineHandle) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }
    
    let handle = &*handle;
    
    match handle.event_queue.lock() {
        Ok(mut queue) => {
            queue.clear();
            SUCCESS
        }
        Err(_) => ERROR_LOCK_FAILED,
    }
}

/// Get the number of pending events
///
/// # Safety
/// The handle must be valid.
#[no_mangle]
pub unsafe extern "C" fn runetika_event_count(handle: *mut EngineHandle) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }
    
    let handle = &*handle;
    
    match handle.event_queue.lock() {
        Ok(queue) => queue.len() as i32,
        Err(_) => ERROR_LOCK_FAILED,
    }
}