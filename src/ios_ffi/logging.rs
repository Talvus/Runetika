/// Logging Bridge for iOS
/// 
/// This module provides logging integration between Rust and iOS's os_log system.

use super::*;
use std::ffi::{CString, CStr};
use bevy::log::{debug, info, error};

/// Log a message at the specified level
///
/// # Safety
/// The handle must be valid and the message must be a valid C string.
#[no_mangle]
pub unsafe extern "C" fn runetika_log(
    handle: *mut EngineHandle,
    level: u32,
    message: *const c_char,
) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }
    
    if message.is_null() {
        return ERROR_INVALID_PARAMETER;
    }
    
    let handle = &*handle;
    
    // Convert C string to Rust string
    let message = match CStr::from_ptr(message).to_str() {
        Ok(s) => s,
        Err(_) => return ERROR_INVALID_PARAMETER,
    };
    
    // Get log callback if set
    if let Ok(callbacks) = handle.callbacks.lock() {
        if let Some(callback) = callbacks.log_callback {
            let c_message = match CString::new(message) {
                Ok(s) => s,
                Err(_) => return ERROR_INVALID_PARAMETER,
            };
            callback(level, c_message.as_ptr());
        }
    }
    
    // Also log to Rust's logging system
    match LogLevel::from_raw(level) {
        LogLevel::Debug => debug!("{}", message),
        LogLevel::Info => info!("{}", message),
        LogLevel::Default => info!("{}", message),
        LogLevel::Error => error!("{}", message),
        LogLevel::Fault => error!("FAULT: {}", message),
    }
    
    SUCCESS
}

impl LogLevel {
    fn from_raw(raw: u32) -> Self {
        match raw {
            0 => LogLevel::Debug,
            1 => LogLevel::Info,
            2 => LogLevel::Default,
            3 => LogLevel::Error,
            4 => LogLevel::Fault,
            _ => LogLevel::Default,
        }
    }
}

/// Set up Rust logging to forward to iOS
pub fn setup_ios_logging(handle: &EngineHandle) {
    // Set up a custom logger that forwards to iOS
    struct IOSLogger {
        handle: std::sync::Weak<Mutex<CallbackRegistry>>,
    }
    
    impl log::Log for IOSLogger {
        fn enabled(&self, metadata: &log::Metadata) -> bool {
            metadata.level() <= log::Level::Debug
        }
        
        fn log(&self, record: &log::Record) {
            if !self.enabled(record.metadata()) {
                return;
            }
            
            if let Some(callbacks) = self.handle.upgrade() {
                if let Ok(callbacks) = callbacks.lock() {
                    if let Some(callback) = callbacks.log_callback {
                        let level = match record.level() {
                            log::Level::Error => LogLevel::Error as u32,
                            log::Level::Warn => LogLevel::Error as u32,
                            log::Level::Info => LogLevel::Info as u32,
                            log::Level::Debug => LogLevel::Debug as u32,
                            log::Level::Trace => LogLevel::Debug as u32,
                        };
                        
                        let message = format!("[{}] {}", record.target(), record.args());
                        if let Ok(c_message) = CString::new(message) {
                            unsafe {
                                callback(level, c_message.as_ptr());
                            }
                        }
                    }
                }
            }
        }
        
        fn flush(&self) {}
    }
}

/// Log a debug message
///
/// # Safety
/// The message must be a valid C string.
#[no_mangle]
pub unsafe extern "C" fn runetika_log_debug(message: *const c_char) -> i32 {
    log_at_level(LogLevel::Debug, message)
}

/// Log an info message
///
/// # Safety
/// The message must be a valid C string.
#[no_mangle]
pub unsafe extern "C" fn runetika_log_info(message: *const c_char) -> i32 {
    log_at_level(LogLevel::Info, message)
}

/// Log an error message
///
/// # Safety
/// The message must be a valid C string.
#[no_mangle]
pub unsafe extern "C" fn runetika_log_error(message: *const c_char) -> i32 {
    log_at_level(LogLevel::Error, message)
}

/// Helper function to log at a specific level
unsafe fn log_at_level(level: LogLevel, message: *const c_char) -> i32 {
    if message.is_null() {
        return ERROR_INVALID_PARAMETER;
    }
    
    let message = match CStr::from_ptr(message).to_str() {
        Ok(s) => s,
        Err(_) => return ERROR_INVALID_PARAMETER,
    };
    
    // Try to get the global engine state
    if let Some(state) = crate::ios_ffi::ENGINE_STATE.read().as_ref() {
        if let Ok(callbacks) = state.callbacks.lock() {
            if let Some(callback) = callbacks.log_callback {
                let c_message = match CString::new(message) {
                    Ok(s) => s,
                    Err(_) => return ERROR_INVALID_PARAMETER,
                };
                callback(level as u32, c_message.as_ptr());
            }
        }
    }
    
    // Also log to Rust's logging system
    match level {
        LogLevel::Debug => debug!("{}", message),
        LogLevel::Info => info!("{}", message),
        LogLevel::Default => info!("{}", message),
        LogLevel::Error => error!("{}", message),
        LogLevel::Fault => error!("FAULT: {}", message),
    }
    
    SUCCESS
}

/// Flush any pending log messages
///
/// # Safety
/// The handle must be valid.
#[no_mangle]
pub unsafe extern "C" fn runetika_log_flush(handle: *mut EngineHandle) -> i32 {
    if handle.is_null() {
        return ERROR_NULL_HANDLE;
    }
    
    // In a real implementation, this might flush buffered logs
    SUCCESS
}