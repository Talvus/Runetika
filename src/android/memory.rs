/// Memory Management for JNI
/// Handles safe memory operations across JVM boundaries

use jni::objects::{GlobalRef, JObject};
use jni::JNIEnv;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use crate::android::jni_bridge::JniError;

/// Reference type for JNI objects
#[derive(Debug, Clone)]
pub enum JniReference {
    Local(JObject<'static>),
    Global(GlobalRef),
}

/// Memory manager for JNI references
pub struct JniMemoryManager {
    global_refs: Arc<Mutex<HashMap<usize, GlobalRef>>>,
    ref_counter: Arc<Mutex<usize>>,
}

impl JniMemoryManager {
    /// Create new memory manager
    pub fn new() -> Self {
        Self {
            global_refs: Arc::new(Mutex::new(HashMap::new())),
            ref_counter: Arc::new(Mutex::new(0)),
        }
    }

    /// Create global reference
    pub fn create_global_ref(env: &JNIEnv, obj: JObject) -> Result<usize, JniError> {
        let global_ref = env.new_global_ref(obj)
            .map_err(|e| JniError::MemoryError(e.to_string()))?;
        
        let manager = Self::instance();
        let id = manager.store_global_ref(global_ref);
        
        Ok(id)
    }

    /// Get global reference by ID
    pub fn get_global_ref(id: usize) -> Option<GlobalRef> {
        let manager = Self::instance();
        manager.global_refs
            .lock()
            .ok()?
            .get(&id)
            .cloned()
    }

    /// Delete global reference
    pub fn delete_global_ref(id: usize) -> Result<(), JniError> {
        let manager = Self::instance();
        manager.global_refs
            .lock()
            .map_err(|e| JniError::ThreadError(e.to_string()))?
            .remove(&id);
        
        Ok(())
    }

    /// Store global reference and return ID
    fn store_global_ref(&self, global_ref: GlobalRef) -> usize {
        let mut counter = self.ref_counter.lock().unwrap();
        let id = *counter;
        *counter += 1;
        
        let mut refs = self.global_refs.lock().unwrap();
        refs.insert(id, global_ref);
        
        id
    }

    /// Get singleton instance
    fn instance() -> &'static Self {
        static mut INSTANCE: Option<JniMemoryManager> = None;
        static INIT: std::sync::Once = std::sync::Once::new();
        
        unsafe {
            INIT.call_once(|| {
                INSTANCE = Some(JniMemoryManager::new());
            });
            INSTANCE.as_ref().unwrap()
        }
    }

    /// Get current memory usage
    pub fn get_usage() -> usize {
        let manager = Self::instance();
        manager.global_refs
            .lock()
            .map(|refs| refs.len() * std::mem::size_of::<GlobalRef>())
            .unwrap_or(0)
    }

    /// Clear all references (for cleanup)
    pub fn clear_all() -> Result<(), JniError> {
        let manager = Self::instance();
        manager.global_refs
            .lock()
            .map_err(|e| JniError::ThreadError(e.to_string()))?
            .clear();
        
        Ok(())
    }
}

/// Auto-release guard for local references
pub struct LocalRefGuard<'a> {
    env: &'a JNIEnv<'a>,
    obj: JObject<'a>,
}

impl<'a> LocalRefGuard<'a> {
    /// Create new local reference guard
    pub fn new(env: &'a JNIEnv<'a>, obj: JObject<'a>) -> Self {
        Self { env, obj }
    }

    /// Get the object
    pub fn get(&self) -> JObject<'a> {
        self.obj
    }
}

impl<'a> Drop for LocalRefGuard<'a> {
    fn drop(&mut self) {
        // Local references are automatically cleaned up by JNI
        // but we can explicitly delete them for better memory management
        let _ = self.env.delete_local_ref(self.obj);
    }
}

/// Safe array access wrapper
pub struct JniArray<'a> {
    env: &'a JNIEnv<'a>,
    array: jni::sys::jarray,
    elements: *mut std::ffi::c_void,
    length: usize,
}

impl<'a> JniArray<'a> {
    /// Create new array accessor
    pub fn new_byte_array(env: &'a JNIEnv<'a>, array: jni::sys::jbyteArray) -> Result<Self, JniError> {
        let length = env.get_array_length(array)
            .map_err(|e| JniError::MemoryError(e.to_string()))? as usize;
        
        let elements = env.get_byte_array_elements(array)
            .map_err(|e| JniError::MemoryError(e.to_string()))?
            .as_ptr() as *mut std::ffi::c_void;
        
        Ok(Self {
            env,
            array: array as jni::sys::jarray,
            elements,
            length,
        })
    }

    /// Get array as slice
    pub fn as_slice<T>(&self) -> &[T] {
        unsafe {
            std::slice::from_raw_parts(self.elements as *const T, self.length)
        }
    }

    /// Get mutable slice
    pub fn as_mut_slice<T>(&mut self) -> &mut [T] {
        unsafe {
            std::slice::from_raw_parts_mut(self.elements as *mut T, self.length)
        }
    }
}

impl<'a> Drop for JniArray<'a> {
    fn drop(&mut self) {
        // Release array elements back to JVM
        // In real implementation, would call appropriate release function
    }
}