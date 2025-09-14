/// Error Handling for FFI
/// 
/// This module provides comprehensive error handling and reporting across the FFI boundary.

use super::*;
use std::ffi::CString;

/// Last error information for debugging
thread_local! {
    static LAST_ERROR: std::cell::RefCell<Option<String>> = std::cell::RefCell::new(None);
}

/// Set the last error message
pub fn set_last_error(error: String) {
    LAST_ERROR.with(|e| {
        *e.borrow_mut() = Some(error);
    });
}

/// Get the last error message
///
/// # Safety
/// The returned pointer is only valid until the next FFI call.
#[no_mangle]
pub unsafe extern "C" fn runetika_get_last_error() -> *const c_char {
    LAST_ERROR.with(|e| {
        match e.borrow().as_ref() {
            Some(error) => {
                match CString::new(error.as_str()) {
                    Ok(c_str) => c_str.into_raw(),
                    Err(_) => ptr::null(),
                }
            }
            None => ptr::null(),
        }
    })
}

/// Clear the last error
#[no_mangle]
pub extern "C" fn runetika_clear_last_error() {
    LAST_ERROR.with(|e| {
        *e.borrow_mut() = None;
    });
}

/// Check if there is a pending error
#[no_mangle]
pub extern "C" fn runetika_has_error() -> bool {
    LAST_ERROR.with(|e| e.borrow().is_some())
}

/// Convert an error code to a human-readable string
///
/// # Safety
/// The returned pointer is static and doesn't need to be freed.
#[no_mangle]
pub unsafe extern "C" fn runetika_error_string(error_code: i32) -> *const c_char {
    let error_str = match error_code {
        SUCCESS => "Success",
        ERROR_NULL_HANDLE => "Null handle",
        ERROR_INVALID_CONFIG => "Invalid configuration",
        ERROR_INIT_FAILED => "Initialization failed",
        ERROR_ALREADY_INITIALIZED => "Already initialized",
        ERROR_LOCK_FAILED => "Lock failed",
        ERROR_INVALID_PARAMETER => "Invalid parameter",
        ERROR_ACTIVE_REFERENCES => "Active references exist",
        ERROR_RUNTIME => "Runtime error",
        ERROR_OUT_OF_MEMORY => "Out of memory",
        ERROR_INVALID_STATE => "Invalid state",
        _ => "Unknown error",
    };
    
    static mut ERROR_STRINGS: Vec<CString> = Vec::new();
    
    // Cache the error strings
    if ERROR_STRINGS.is_empty() {
        ERROR_STRINGS = vec![
            CString::new("Success").unwrap(),
            CString::new("Null handle").unwrap(),
            CString::new("Invalid configuration").unwrap(),
            CString::new("Initialization failed").unwrap(),
            CString::new("Already initialized").unwrap(),
            CString::new("Lock failed").unwrap(),
            CString::new("Invalid parameter").unwrap(),
            CString::new("Active references exist").unwrap(),
            CString::new("Runtime error").unwrap(),
            CString::new("Out of memory").unwrap(),
            CString::new("Invalid state").unwrap(),
            CString::new("Unknown error").unwrap(),
        ];
    }
    
    let index = match error_code {
        SUCCESS => 0,
        ERROR_NULL_HANDLE => 1,
        ERROR_INVALID_CONFIG => 2,
        ERROR_INIT_FAILED => 3,
        ERROR_ALREADY_INITIALIZED => 4,
        ERROR_LOCK_FAILED => 5,
        ERROR_INVALID_PARAMETER => 6,
        ERROR_ACTIVE_REFERENCES => 7,
        ERROR_RUNTIME => 8,
        ERROR_OUT_OF_MEMORY => 9,
        ERROR_INVALID_STATE => 10,
        _ => 11,
    };
    
    ERROR_STRINGS[index].as_ptr()
}

/// Panic handler that converts Rust panics to FFI errors
pub fn setup_panic_handler() {
    std::panic::set_hook(Box::new(|panic_info| {
        let msg = if let Some(s) = panic_info.payload().downcast_ref::<&str>() {
            s.to_string()
        } else if let Some(s) = panic_info.payload().downcast_ref::<String>() {
            s.clone()
        } else {
            "Unknown panic".to_string()
        };
        
        let location = if let Some(loc) = panic_info.location() {
            format!(" at {}:{}:{}", loc.file(), loc.line(), loc.column())
        } else {
            String::new()
        };
        
        let full_msg = format!("Rust panic: {}{}", msg, location);
        set_last_error(full_msg.clone());
        
        // Try to notify Swift via callback
        if let Some(state) = crate::ios_ffi::ENGINE_STATE.read().as_ref() {
            if let Ok(callbacks) = state.callbacks.lock() {
                if let Some(callback) = callbacks.error_callback {
                    if let Ok(c_msg) = CString::new(full_msg) {
                        unsafe {
                            callback(ERROR_RUNTIME, c_msg.as_ptr());
                        }
                    }
                }
            }
        }
    }));
}

/// Result type for FFI operations
pub type FFIResult<T> = Result<T, FFIError>;

/// FFI error type
#[derive(Debug, Clone)]
pub enum FFIError {
    NullHandle,
    InvalidConfig(String),
    InitFailed(String),
    AlreadyInitialized,
    LockFailed,
    InvalidParameter(String),
    ActiveReferences(u32),
    Runtime(String),
    OutOfMemory,
    InvalidState(String),
}

impl FFIError {
    /// Convert to error code
    pub fn to_code(&self) -> i32 {
        match self {
            FFIError::NullHandle => ERROR_NULL_HANDLE,
            FFIError::InvalidConfig(_) => ERROR_INVALID_CONFIG,
            FFIError::InitFailed(_) => ERROR_INIT_FAILED,
            FFIError::AlreadyInitialized => ERROR_ALREADY_INITIALIZED,
            FFIError::LockFailed => ERROR_LOCK_FAILED,
            FFIError::InvalidParameter(_) => ERROR_INVALID_PARAMETER,
            FFIError::ActiveReferences(_) => ERROR_ACTIVE_REFERENCES,
            FFIError::Runtime(_) => ERROR_RUNTIME,
            FFIError::OutOfMemory => ERROR_OUT_OF_MEMORY,
            FFIError::InvalidState(_) => ERROR_INVALID_STATE,
        }
    }
    
    /// Get error message
    pub fn message(&self) -> String {
        match self {
            FFIError::NullHandle => "Null handle provided".to_string(),
            FFIError::InvalidConfig(msg) => format!("Invalid configuration: {}", msg),
            FFIError::InitFailed(msg) => format!("Initialization failed: {}", msg),
            FFIError::AlreadyInitialized => "Engine already initialized".to_string(),
            FFIError::LockFailed => "Failed to acquire lock".to_string(),
            FFIError::InvalidParameter(msg) => format!("Invalid parameter: {}", msg),
            FFIError::ActiveReferences(count) => format!("Active references exist: {}", count),
            FFIError::Runtime(msg) => format!("Runtime error: {}", msg),
            FFIError::OutOfMemory => "Out of memory".to_string(),
            FFIError::InvalidState(msg) => format!("Invalid state: {}", msg),
        }
    }
}

impl std::fmt::Display for FFIError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message())
    }
}

impl std::error::Error for FFIError {}

/// Macro for safely executing FFI operations
#[macro_export]
macro_rules! ffi_try {
    ($expr:expr) => {
        match $expr {
            Ok(val) => val,
            Err(e) => {
                set_last_error(e.message());
                return e.to_code();
            }
        }
    };
}