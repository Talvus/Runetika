/// Memory Management for FFI
/// 
/// This module provides safe memory allocation and deallocation across the FFI boundary.

use super::*;
use std::alloc::{alloc, dealloc, Layout};
use std::sync::atomic::{AtomicU64, Ordering};

/// Global memory statistics
static ALLOCATED_BYTES: AtomicU64 = AtomicU64::new(0);
static ALLOCATION_COUNT: AtomicU64 = AtomicU64::new(0);
static PEAK_BYTES: AtomicU64 = AtomicU64::new(0);
static DEALLOCATION_COUNT: AtomicU64 = AtomicU64::new(0);

/// Allocate memory that can be safely passed to Swift
///
/// # Safety
/// The returned pointer must be freed with runetika_free.
#[no_mangle]
pub unsafe extern "C" fn runetika_alloc(size: usize) -> *mut u8 {
    if size == 0 {
        return ptr::null_mut();
    }
    
    let layout = match Layout::from_size_align(size, 8) {
        Ok(l) => l,
        Err(_) => return ptr::null_mut(),
    };
    
    let ptr = alloc(layout);
    if !ptr.is_null() {
        // Update statistics
        ALLOCATED_BYTES.fetch_add(size as u64, Ordering::Relaxed);
        ALLOCATION_COUNT.fetch_add(1, Ordering::Relaxed);
        
        // Update peak if necessary
        let current = ALLOCATED_BYTES.load(Ordering::Relaxed);
        let mut peak = PEAK_BYTES.load(Ordering::Relaxed);
        while current > peak {
            match PEAK_BYTES.compare_exchange_weak(
                peak,
                current,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(p) => peak = p,
            }
        }
    }
    
    ptr
}

/// Free memory allocated with runetika_alloc
///
/// # Safety
/// The pointer must have been allocated with runetika_alloc and the size must match.
#[no_mangle]
pub unsafe extern "C" fn runetika_free(ptr: *mut u8, size: usize) {
    if ptr.is_null() || size == 0 {
        return;
    }
    
    let layout = match Layout::from_size_align(size, 8) {
        Ok(l) => l,
        Err(_) => return,
    };
    
    dealloc(ptr, layout);
    
    // Update statistics
    ALLOCATED_BYTES.fetch_sub(size as u64, Ordering::Relaxed);
    DEALLOCATION_COUNT.fetch_add(1, Ordering::Relaxed);
}

/// Allocate and zero-initialize memory
///
/// # Safety
/// The returned pointer must be freed with runetika_free.
#[no_mangle]
pub unsafe extern "C" fn runetika_calloc(count: usize, size: usize) -> *mut u8 {
    let total_size = match count.checked_mul(size) {
        Some(s) => s,
        None => return ptr::null_mut(),
    };
    
    let ptr = runetika_alloc(total_size);
    if !ptr.is_null() {
        std::ptr::write_bytes(ptr, 0, total_size);
    }
    
    ptr
}

/// Reallocate memory
///
/// # Safety
/// The old pointer must have been allocated with runetika_alloc.
#[no_mangle]
pub unsafe extern "C" fn runetika_realloc(
    old_ptr: *mut u8,
    old_size: usize,
    new_size: usize,
) -> *mut u8 {
    if new_size == 0 {
        if !old_ptr.is_null() {
            runetika_free(old_ptr, old_size);
        }
        return ptr::null_mut();
    }
    
    if old_ptr.is_null() {
        return runetika_alloc(new_size);
    }
    
    let new_ptr = runetika_alloc(new_size);
    if !new_ptr.is_null() {
        let copy_size = old_size.min(new_size);
        std::ptr::copy_nonoverlapping(old_ptr, new_ptr, copy_size);
        runetika_free(old_ptr, old_size);
    }
    
    new_ptr
}

/// Copy a Rust string to a C string that Swift can use
///
/// # Safety
/// The returned pointer must be freed with runetika_free_string.
#[no_mangle]
pub unsafe extern "C" fn runetika_string_create(rust_str: &str) -> *mut c_char {
    match CString::new(rust_str) {
        Ok(c_str) => {
            let bytes = c_str.as_bytes_with_nul();
            let ptr = runetika_alloc(bytes.len()) as *mut c_char;
            if !ptr.is_null() {
                std::ptr::copy_nonoverlapping(bytes.as_ptr() as *const c_char, ptr, bytes.len());
            }
            ptr
        }
        Err(_) => ptr::null_mut(),
    }
}

/// Free a string created with runetika_string_create
///
/// # Safety
/// The pointer must have been created with runetika_string_create.
#[no_mangle]
pub unsafe extern "C" fn runetika_string_free(ptr: *mut c_char) {
    if ptr.is_null() {
        return;
    }
    
    let len = CStr::from_ptr(ptr).to_bytes_with_nul().len();
    runetika_free(ptr as *mut u8, len);
}

/// Create a buffer that can be shared with Swift
///
/// # Safety
/// The returned pointer must be freed with runetika_buffer_free.
#[no_mangle]
pub unsafe extern "C" fn runetika_buffer_create(data: &[u8]) -> *mut BufferHandle {
    let handle = Box::new(BufferHandle {
        data: runetika_alloc(data.len()),
        size: data.len(),
        capacity: data.len(),
    });
    
    if !handle.data.is_null() {
        std::ptr::copy_nonoverlapping(data.as_ptr(), handle.data, data.len());
        Box::into_raw(handle)
    } else {
        ptr::null_mut()
    }
}

/// Free a buffer handle
///
/// # Safety
/// The handle must have been created with runetika_buffer_create.
#[no_mangle]
pub unsafe extern "C" fn runetika_buffer_free(handle: *mut BufferHandle) {
    if handle.is_null() {
        return;
    }
    
    let handle = Box::from_raw(handle);
    if !handle.data.is_null() {
        runetika_free(handle.data, handle.capacity);
    }
}

/// Buffer handle for passing data to Swift
#[repr(C)]
pub struct BufferHandle {
    pub data: *mut u8,
    pub size: usize,
    pub capacity: usize,
}

/// Get current memory statistics
///
/// # Safety
/// The stats pointer must be valid.
#[no_mangle]
pub unsafe extern "C" fn runetika_memory_stats(stats: *mut MemoryStats) -> i32 {
    if stats.is_null() {
        return ERROR_NULL_HANDLE;
    }
    
    (*stats).allocated_bytes = ALLOCATED_BYTES.load(Ordering::Relaxed);
    (*stats).allocation_count = ALLOCATION_COUNT.load(Ordering::Relaxed);
    (*stats).peak_bytes = PEAK_BYTES.load(Ordering::Relaxed);
    (*stats).deallocation_count = DEALLOCATION_COUNT.load(Ordering::Relaxed);
    
    SUCCESS
}

/// Reset memory statistics
#[no_mangle]
pub extern "C" fn runetika_memory_stats_reset() {
    ALLOCATED_BYTES.store(0, Ordering::Relaxed);
    ALLOCATION_COUNT.store(0, Ordering::Relaxed);
    PEAK_BYTES.store(0, Ordering::Relaxed);
    DEALLOCATION_COUNT.store(0, Ordering::Relaxed);
}

/// Get performance metrics
///
/// # Safety
/// The handle and metrics pointer must be valid.
#[no_mangle]
pub unsafe extern "C" fn runetika_get_performance_metrics(
    handle: *mut EngineHandle,
    metrics: *mut PerformanceMetrics,
) -> i32 {
    if handle.is_null() || metrics.is_null() {
        return ERROR_NULL_HANDLE;
    }
    
    let handle = &*handle;
    
    // Get memory stats
    runetika_memory_stats(&mut (*metrics).memory);
    
    // Get other metrics from the engine
    match handle.app.lock() {
        Ok(app) => {
            // In a real implementation, we'd query the engine for these metrics
            // For now, return placeholder values
            (*metrics).fps = 60.0;
            (*metrics).frame_time_ms = 16.67;
            (*metrics).update_time_ms = 8.0;
            (*metrics).render_time_ms = 8.0;
            (*metrics).draw_calls = 100;
            (*metrics).entity_count = 1000;
            
            SUCCESS
        }
        Err(_) => ERROR_LOCK_FAILED,
    }
}