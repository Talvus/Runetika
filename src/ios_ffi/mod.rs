/// iOS FFI Bridge Module
/// 
/// This module provides a C-compatible Foreign Function Interface for Swift/iOS integration.
/// It enables safe bidirectional communication between Rust/Bevy and iOS native code.
///
/// # Architecture
/// 
/// The FFI bridge follows these principles:
/// - Memory safety through opaque handles and explicit ownership transfer
/// - Thread safety via message passing and atomic operations
/// - Error handling through result codes and error callbacks
/// - Event system for iOS → Bevy communication
/// - Minimal data copying across language boundaries

use std::ffi::{c_char, c_void, CStr, CString};
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::ptr;
use std::panic;
use std::mem;
use parking_lot::RwLock;

pub mod types;
pub mod engine;
pub mod events;
pub mod logging;
pub mod memory;
pub mod error;

pub use types::*;
pub use engine::*;
pub use events::*;
pub use logging::*;
pub use memory::*;
pub use error::*;

/// Global engine state for thread-safe access
static ENGINE_STATE: RwLock<Option<Arc<EngineHandle>>> = RwLock::new(None);

/// Initialization guard to prevent multiple initializations
static INITIALIZED: AtomicBool = AtomicBool::new(false);

/// Reference counter for tracking active Swift references
static SWIFT_REF_COUNT: AtomicU32 = AtomicU32::new(0);

/// Engine handle that Swift holds as an opaque pointer
pub struct EngineHandle {
    /// The Bevy App instance
    app: Arc<Mutex<bevy::app::App>>,
    /// Event queue for iOS → Bevy events
    event_queue: Arc<Mutex<Vec<IOSEvent>>>,
    /// Callback registry for Swift callbacks
    callbacks: Arc<Mutex<CallbackRegistry>>,
    /// Thread handle for the render thread
    render_thread: Option<std::thread::JoinHandle<()>>,
    /// Shutdown flag
    should_shutdown: Arc<AtomicBool>,
}

/// Callback registry for Swift function pointers
pub struct CallbackRegistry {
    /// Error callback
    error_callback: Option<ErrorCallback>,
    /// Log callback
    log_callback: Option<LogCallback>,
    /// Frame rendered callback
    frame_callback: Option<FrameCallback>,
    /// Event processed callback
    event_callback: Option<EventCallback>,
}

/// Initialize the Runetika engine for iOS
///
/// # Safety
/// This function must be called exactly once from the main thread.
/// The returned handle must be kept alive for the duration of the app.
#[no_mangle]
pub unsafe extern "C" fn runetika_init(
    config: *const EngineConfig,
    error_callback: ErrorCallback,
) -> *mut EngineHandle {
    // Prevent double initialization
    if INITIALIZED.swap(true, Ordering::SeqCst) {
        if let Some(callback) = error_callback {
            let error = CString::new("Engine already initialized").unwrap();
            callback(ERROR_ALREADY_INITIALIZED, error.as_ptr());
        }
        return ptr::null_mut();
    }

    // Set panic hook to forward to Swift
    panic::set_hook(Box::new(move |panic_info| {
        let msg = format!("Rust panic: {}", panic_info);
        log_error(&msg);
    }));

    // Parse configuration
    let config = if config.is_null() {
        EngineConfig::default()
    } else {
        match EngineConfig::from_raw(&*config) {
            Ok(c) => c,
            Err(e) => {
                if let Some(callback) = error_callback {
                    let error = CString::new(format!("Invalid config: {}", e)).unwrap();
                    callback(ERROR_INVALID_CONFIG, error.as_ptr());
                }
                return ptr::null_mut();
            }
        }
    };

    // Create the engine handle
    match create_engine(config, error_callback) {
        Ok(handle) => {
            let handle = Arc::new(handle);
            *ENGINE_STATE.write() = Some(handle.clone());
            Arc::into_raw(handle) as *mut EngineHandle
        }
        Err(e) => {
            INITIALIZED.store(false, Ordering::SeqCst);
            if let Some(callback) = error_callback {
                let error = CString::new(format!("Engine creation failed: {}", e)).unwrap();
                callback(ERROR_INIT_FAILED, error.as_ptr());
            }
            ptr::null_mut()
        }
    }
}

/// Update the engine for one frame
///
/// # Safety
/// The handle must be valid and initialized.
/// This should be called from the main thread or a dedicated update thread.
#[no_mangle]
pub unsafe extern "C" fn runetika_update(
    handle: *mut EngineHandle,
    delta_time: f32,
) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }

    let handle = &*handle;
    
    // Process queued iOS events
    process_event_queue(handle);
    
    // Update the Bevy app
    match handle.app.lock() {
        Ok(mut app) => {
            // Set delta time if needed
            // app.world.resource_mut::<Time>().update_with_instant(...);
            app.update();
            SUCCESS
        }
        Err(_) => ERROR_LOCK_FAILED,
    }
}

/// Render the current frame
///
/// # Safety
/// The handle must be valid and initialized.
/// This should be called from the render thread with a valid GL context.
#[no_mangle]
pub unsafe extern "C" fn runetika_render(
    handle: *mut EngineHandle,
    framebuffer: u32,
    width: u32,
    height: u32,
) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }

    let handle = &*handle;
    
    // Update viewport if needed
    match handle.app.lock() {
        Ok(mut app) => {
            // Update render target and viewport
            // This would integrate with Bevy's rendering system
            // For now, we just trigger the render systems
            
            // Notify frame callback if set
            if let Ok(callbacks) = handle.callbacks.lock() {
                if let Some(callback) = callbacks.frame_callback {
                    callback(framebuffer, width, height);
                }
            }
            
            SUCCESS
        }
        Err(_) => ERROR_LOCK_FAILED,
    }
}

/// Shutdown the engine and release all resources
///
/// # Safety
/// The handle must be valid. After calling this, the handle is invalid.
#[no_mangle]
pub unsafe extern "C" fn runetika_shutdown(handle: *mut EngineHandle) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }

    // Check if there are still active Swift references
    if SWIFT_REF_COUNT.load(Ordering::SeqCst) > 0 {
        return ERROR_ACTIVE_REFERENCES;
    }

    // Take ownership of the handle
    let handle = Arc::from_raw(handle);
    
    // Signal shutdown
    handle.should_shutdown.store(true, Ordering::SeqCst);
    
    // Clear global state
    *ENGINE_STATE.write() = None;
    INITIALIZED.store(false, Ordering::SeqCst);
    
    // The handle will be dropped here, cleaning up resources
    SUCCESS
}

/// Send a touch event to the engine
///
/// # Safety
/// The handle must be valid and initialized.
#[no_mangle]
pub unsafe extern "C" fn runetika_send_touch(
    handle: *mut EngineHandle,
    touch_id: u64,
    phase: u32,
    x: f32,
    y: f32,
    force: f32,
) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }

    let handle = &*handle;
    
    let event = IOSEvent::Touch(TouchEvent {
        id: touch_id,
        phase: TouchPhase::from_raw(phase),
        position: (x, y),
        force,
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

/// Send accelerometer data to the engine
///
/// # Safety
/// The handle must be valid and initialized.
#[no_mangle]
pub unsafe extern "C" fn runetika_send_accelerometer(
    handle: *mut EngineHandle,
    x: f32,
    y: f32,
    z: f32,
) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }

    let handle = &*handle;
    
    let event = IOSEvent::Accelerometer(AccelerometerEvent {
        acceleration: (x, y, z),
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

/// Set a callback for error reporting
///
/// # Safety
/// The handle must be valid. The callback must remain valid for the lifetime of the engine.
#[no_mangle]
pub unsafe extern "C" fn runetika_set_error_callback(
    handle: *mut EngineHandle,
    callback: ErrorCallback,
) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }

    let handle = &*handle;
    
    match handle.callbacks.lock() {
        Ok(mut callbacks) => {
            callbacks.error_callback = callback;
            SUCCESS
        }
        Err(_) => ERROR_LOCK_FAILED,
    }
}

/// Set a callback for log messages
///
/// # Safety
/// The handle must be valid. The callback must remain valid for the lifetime of the engine.
#[no_mangle]
pub unsafe extern "C" fn runetika_set_log_callback(
    handle: *mut EngineHandle,
    callback: LogCallback,
) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }

    let handle = &*handle;
    
    match handle.callbacks.lock() {
        Ok(mut callbacks) => {
            callbacks.log_callback = callback;
            SUCCESS
        }
        Err(_) => ERROR_LOCK_FAILED,
    }
}

/// Retain a Swift reference to prevent deallocation
///
/// # Safety
/// Must be balanced with a corresponding release call.
#[no_mangle]
pub unsafe extern "C" fn runetika_retain() -> u32 {
    SWIFT_REF_COUNT.fetch_add(1, Ordering::SeqCst) + 1
}

/// Release a Swift reference
///
/// # Safety
/// Must be called once for each retain call.
#[no_mangle]
pub unsafe extern "C" fn runetika_release() -> u32 {
    let count = SWIFT_REF_COUNT.fetch_sub(1, Ordering::SeqCst);
    if count == 0 {
        panic!("Released more references than retained!");
    }
    count - 1
}

/// Get the current Swift reference count
#[no_mangle]
pub extern "C" fn runetika_ref_count() -> u32 {
    SWIFT_REF_COUNT.load(Ordering::SeqCst)
}

/// Check if the engine is initialized
#[no_mangle]
pub extern "C" fn runetika_is_initialized() -> bool {
    INITIALIZED.load(Ordering::SeqCst)
}

/// Get version information
#[no_mangle]
pub extern "C" fn runetika_version() -> *const c_char {
    static VERSION: &[u8] = b"0.1.0\0";
    VERSION.as_ptr() as *const c_char
}

// Helper function to process the event queue
fn process_event_queue(handle: &EngineHandle) {
    if let Ok(mut queue) = handle.event_queue.lock() {
        if let Ok(mut app) = handle.app.lock() {
            for event in queue.drain(..) {
                // Send events to Bevy's event system
                // app.world.send_event(event);
                
                // Notify callback if set
                if let Ok(callbacks) = handle.callbacks.lock() {
                    if let Some(callback) = callbacks.event_callback {
                        callback(event.as_raw_type(), event.as_raw_data());
                    }
                }
            }
        }
    }
}

// Helper function to log errors
fn log_error(msg: &str) {
    if let Some(state) = ENGINE_STATE.read().as_ref() {
        if let Ok(callbacks) = state.callbacks.lock() {
            if let Some(callback) = callbacks.error_callback {
                if let Ok(c_msg) = CString::new(msg) {
                    unsafe { callback(ERROR_RUNTIME, c_msg.as_ptr()); }
                }
            }
        }
    }
}