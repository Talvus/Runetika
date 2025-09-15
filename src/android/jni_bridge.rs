/// JNI Bridge Core Implementation
/// Provides the main JNI interface for Android integration
/// 
/// This module handles:
/// - JNI function exports with proper signatures
/// - Safe memory management across JVM boundaries
/// - Thread-safe initialization and shutdown
/// - Exception handling and error propagation

use jni::objects::{GlobalRef, JClass, JObject, JString, JValue};
use jni::sys::{jboolean, jfloat, jint, jlong, JNI_VERSION_1_6};
use jni::{JNIEnv, JavaVM};
use std::sync::{Arc, Mutex, Once};
use std::sync::atomic::{AtomicBool, Ordering};
use bevy::prelude::*;
use crate::android::lifecycle::AndroidLifecycle;
use crate::android::event_handler::EventBridge;
use crate::android::surface_renderer::SurfaceRenderer;
use crate::android::memory::JniMemoryManager;

// Global state management with thread safety
static INIT_ONCE: Once = Once::new();
static mut JAVA_VM: Option<Arc<JavaVM>> = None;
static mut BEVY_APP: Option<Arc<Mutex<App>>> = None;
static IS_INITIALIZED: AtomicBool = AtomicBool::new(false);

/// Error types for JNI operations
#[derive(Debug, Clone)]
pub enum JniError {
    InitializationFailed(String),
    InvalidState(String),
    MemoryError(String),
    ThreadError(String),
    BevyError(String),
}

impl std::fmt::Display for JniError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            JniError::InitializationFailed(msg) => write!(f, "JNI initialization failed: {}", msg),
            JniError::InvalidState(msg) => write!(f, "Invalid JNI state: {}", msg),
            JniError::MemoryError(msg) => write!(f, "JNI memory error: {}", msg),
            JniError::ThreadError(msg) => write!(f, "JNI thread error: {}", msg),
            JniError::BevyError(msg) => write!(f, "Bevy error: {}", msg),
        }
    }
}

impl std::error::Error for JniError {}

/// JNI_OnLoad - Called when the native library is loaded
/// This is the entry point for JNI initialization
#[no_mangle]
pub extern "system" fn JNI_OnLoad(vm: JavaVM, _reserved: *mut std::os::raw::c_void) -> jint {
    let env = match vm.get_env() {
        Ok(env) => env,
        Err(e) => {
            eprintln!("Failed to get JNI environment: {:?}", e);
            return JNI_VERSION_1_6;
        }
    };

    // Initialize global JavaVM reference
    unsafe {
        JAVA_VM = Some(Arc::new(vm));
    }

    // Register native methods
    if let Err(e) = register_native_methods(&env) {
        eprintln!("Failed to register native methods: {:?}", e);
    }

    JNI_VERSION_1_6
}

/// Register all native methods with their JNI signatures
fn register_native_methods(env: &JNIEnv) -> Result<(), jni::errors::Error> {
    // Native method registration will be done here
    // This allows for better performance than using Java_* naming convention
    Ok(())
}

/// Initialize the Bevy engine
/// Called from Kotlin: native fun initBevy(assetPath: String, cachePath: String): Long
#[no_mangle]
pub extern "system" fn Java_com_runetika_android_RunteikaNative_initBevy(
    env: JNIEnv,
    _class: JClass,
    asset_path: JString,
    cache_path: JString,
) -> jlong {
    let result = std::panic::catch_unwind(|| {
        init_bevy_internal(env, asset_path, cache_path)
    });

    match result {
        Ok(Ok(handle)) => handle,
        Ok(Err(e)) => {
            let _ = throw_jni_exception(&env, &format!("Bevy initialization failed: {}", e));
            0
        },
        Err(_) => {
            let _ = throw_jni_exception(&env, "Bevy initialization panicked");
            0
        }
    }
}

/// Internal Bevy initialization with proper error handling
fn init_bevy_internal(
    env: JNIEnv,
    asset_path: JString,
    cache_path: JString,
) -> Result<jlong, JniError> {
    if IS_INITIALIZED.load(Ordering::SeqCst) {
        return Err(JniError::InvalidState("Bevy already initialized".to_string()));
    }

    let asset_path_str: String = env.get_string(asset_path)
        .map_err(|e| JniError::MemoryError(e.to_string()))?
        .into();
    
    let cache_path_str: String = env.get_string(cache_path)
        .map_err(|e| JniError::MemoryError(e.to_string()))?
        .into();

    let mut handle = 0i64;
    
    INIT_ONCE.call_once(|| {
        // Create Bevy app with Android-specific configuration
        let mut app = App::new();
        
        // Add Android-specific plugins
        app.add_plugins(MinimalPlugins.set(bevy::log::LogPlugin {
            level: bevy::log::Level::INFO,
            ..default()
        }));

        // Store app instance
        unsafe {
            BEVY_APP = Some(Arc::new(Mutex::new(app)));
            handle = BEVY_APP.as_ref().unwrap().as_ref() as *const _ as i64;
        }
        
        IS_INITIALIZED.store(true, Ordering::SeqCst);
    });

    Ok(handle)
}

/// Update the Bevy engine (called each frame)
/// Called from Kotlin: native fun updateBevy(deltaTime: Float): Boolean
#[no_mangle]
pub extern "system" fn Java_com_runetika_android_RuneikaNative_updateBevy(
    env: JNIEnv,
    _class: JClass,
    delta_time: jfloat,
) -> jboolean {
    let result = std::panic::catch_unwind(|| {
        update_bevy_internal(delta_time)
    });

    match result {
        Ok(Ok(_)) => 1,
        Ok(Err(e)) => {
            let _ = throw_jni_exception(&env, &format!("Bevy update failed: {}", e));
            0
        },
        Err(_) => {
            let _ = throw_jni_exception(&env, "Bevy update panicked");
            0
        }
    }
}

/// Internal Bevy update logic
fn update_bevy_internal(delta_time: f32) -> Result<(), JniError> {
    if !IS_INITIALIZED.load(Ordering::SeqCst) {
        return Err(JniError::InvalidState("Bevy not initialized".to_string()));
    }

    unsafe {
        if let Some(app) = &BEVY_APP {
            let mut app_guard = app.lock()
                .map_err(|e| JniError::ThreadError(e.to_string()))?;
            
            // Update Bevy systems
            app_guard.update();
            
            Ok(())
        } else {
            Err(JniError::InvalidState("No Bevy app instance".to_string()))
        }
    }
}

/// Render the Bevy frame
/// Called from Kotlin: native fun renderBevy(surface: Surface): Boolean
#[no_mangle]
pub extern "system" fn Java_com_runetika_android_RuneikaNative_renderBevy(
    env: JNIEnv,
    _class: JClass,
    surface: JObject,
) -> jboolean {
    let result = std::panic::catch_unwind(|| {
        render_bevy_internal(env, surface)
    });

    match result {
        Ok(Ok(_)) => 1,
        Ok(Err(e)) => {
            let _ = throw_jni_exception(&env, &format!("Bevy render failed: {}", e));
            0
        },
        Err(_) => {
            let _ = throw_jni_exception(&env, "Bevy render panicked");
            0
        }
    }
}

/// Internal Bevy rendering
fn render_bevy_internal(env: JNIEnv, surface: JObject) -> Result<(), JniError> {
    if !IS_INITIALIZED.load(Ordering::SeqCst) {
        return Err(JniError::InvalidState("Bevy not initialized".to_string()));
    }

    // Handle surface rendering
    let surface_ref = env.new_global_ref(surface)
        .map_err(|e| JniError::MemoryError(e.to_string()))?;
    
    // Render frame through surface renderer
    SurfaceRenderer::render_frame(surface_ref)?;
    
    Ok(())
}

/// Shutdown Bevy engine and cleanup resources
/// Called from Kotlin: native fun shutdownBevy(): Boolean
#[no_mangle]
pub extern "system" fn Java_com_runetika_android_RuneikaNative_shutdownBevy(
    env: JNIEnv,
    _class: JClass,
) -> jboolean {
    let result = std::panic::catch_unwind(|| {
        shutdown_bevy_internal()
    });

    match result {
        Ok(Ok(_)) => 1,
        Ok(Err(e)) => {
            let _ = throw_jni_exception(&env, &format!("Bevy shutdown failed: {}", e));
            0
        },
        Err(_) => {
            let _ = throw_jni_exception(&env, "Bevy shutdown panicked");
            0
        }
    }
}

/// Internal Bevy shutdown
fn shutdown_bevy_internal() -> Result<(), JniError> {
    if !IS_INITIALIZED.load(Ordering::SeqCst) {
        return Ok(()); // Already shutdown
    }

    unsafe {
        // Clean up Bevy app
        if let Some(app) = BEVY_APP.take() {
            // App will be dropped here
        }
        
        IS_INITIALIZED.store(false, Ordering::SeqCst);
    }

    Ok(())
}

/// Send touch event to Bevy
/// Called from Kotlin: native fun sendTouchEvent(x: Float, y: Float, action: Int, pointerId: Int): Boolean
#[no_mangle]
pub extern "system" fn Java_com_runetika_android_RuneikaNative_sendTouchEvent(
    env: JNIEnv,
    _class: JClass,
    x: jfloat,
    y: jfloat,
    action: jint,
    pointer_id: jint,
) -> jboolean {
    let result = std::panic::catch_unwind(|| {
        EventBridge::send_touch_event(x, y, action, pointer_id)
    });

    match result {
        Ok(Ok(_)) => 1,
        Ok(Err(e)) => {
            let _ = throw_jni_exception(&env, &format!("Touch event failed: {}", e));
            0
        },
        Err(_) => {
            let _ = throw_jni_exception(&env, "Touch event panicked");
            0
        }
    }
}

/// Send sensor data to Bevy
/// Called from Kotlin: native fun sendSensorData(type: Int, values: FloatArray): Boolean
#[no_mangle]
pub extern "system" fn Java_com_runetika_android_RuneikaNative_sendSensorData(
    env: JNIEnv,
    _class: JClass,
    sensor_type: jint,
    values: JObject,
) -> jboolean {
    let result = std::panic::catch_unwind(|| {
        send_sensor_data_internal(env, sensor_type, values)
    });

    match result {
        Ok(Ok(_)) => 1,
        Ok(Err(e)) => {
            let _ = throw_jni_exception(&env, &format!("Sensor data failed: {}", e));
            0
        },
        Err(_) => {
            let _ = throw_jni_exception(&env, "Sensor data panicked");
            0
        }
    }
}

/// Internal sensor data handling
fn send_sensor_data_internal(env: JNIEnv, sensor_type: i32, values: JObject) -> Result<(), JniError> {
    // Extract float array from JObject
    let float_array = env.get_float_array_elements(values.into_inner())
        .map_err(|e| JniError::MemoryError(e.to_string()))?;
    
    let values_vec: Vec<f32> = unsafe {
        std::slice::from_raw_parts(float_array.as_ptr(), float_array.len())
            .to_vec()
    };
    
    // Send to event bridge
    EventBridge::send_sensor_data(sensor_type, values_vec)?;
    
    Ok(())
}

/// Handle Android lifecycle events
/// Called from Kotlin: native fun onLifecycleEvent(event: Int): Boolean
#[no_mangle]
pub extern "system" fn Java_com_runetika_android_RuneikaNative_onLifecycleEvent(
    env: JNIEnv,
    _class: JClass,
    event: jint,
) -> jboolean {
    let result = std::panic::catch_unwind(|| {
        AndroidLifecycle::handle_event(event)
    });

    match result {
        Ok(Ok(_)) => 1,
        Ok(Err(e)) => {
            let _ = throw_jni_exception(&env, &format!("Lifecycle event failed: {}", e));
            0
        },
        Err(_) => {
            let _ = throw_jni_exception(&env, "Lifecycle event panicked");
            0
        }
    }
}

/// Load asset from APK
/// Called from Kotlin: native fun loadAsset(path: String): ByteArray?
#[no_mangle]
pub extern "system" fn Java_com_runetika_android_RuneikaNative_loadAsset(
    env: JNIEnv,
    _class: JClass,
    path: JString,
) -> JObject {
    let result = std::panic::catch_unwind(|| {
        load_asset_internal(env, path)
    });

    match result {
        Ok(Ok(bytes)) => bytes,
        Ok(Err(e)) => {
            let _ = throw_jni_exception(&env, &format!("Asset load failed: {}", e));
            JObject::null()
        },
        Err(_) => {
            let _ = throw_jni_exception(&env, "Asset load panicked");
            JObject::null()
        }
    }
}

/// Internal asset loading
fn load_asset_internal(env: JNIEnv, path: JString) -> Result<JObject, JniError> {
    let path_str: String = env.get_string(path)
        .map_err(|e| JniError::MemoryError(e.to_string()))?
        .into();
    
    // Load asset through asset loader
    let asset_data = crate::android::asset_loader::AndroidAssetLoader::load(&path_str)?;
    
    // Convert to Java byte array
    let byte_array = env.new_byte_array(asset_data.len() as i32)
        .map_err(|e| JniError::MemoryError(e.to_string()))?;
    
    env.set_byte_array_region(byte_array, 0, &asset_data[..])
        .map_err(|e| JniError::MemoryError(e.to_string()))?;
    
    Ok(JObject::from(byte_array))
}

/// Get current FPS
/// Called from Kotlin: native fun getCurrentFps(): Float
#[no_mangle]
pub extern "system" fn Java_com_runetika_android_RuneikaNative_getCurrentFps(
    _env: JNIEnv,
    _class: JClass,
) -> jfloat {
    // TODO: Implement FPS tracking
    60.0
}

/// Get memory usage
/// Called from Kotlin: native fun getMemoryUsage(): Long
#[no_mangle]
pub extern "system" fn Java_com_runetika_android_RuneikaNative_getMemoryUsage(
    _env: JNIEnv,
    _class: JClass,
) -> jlong {
    JniMemoryManager::get_usage() as jlong
}

/// Utility function to throw Java exceptions
fn throw_jni_exception(env: &JNIEnv, message: &str) -> Result<(), jni::errors::Error> {
    let exception_class = env.find_class("java/lang/RuntimeException")?;
    env.throw_new(exception_class, message)
}

/// Get JavaVM instance
pub fn get_java_vm() -> Option<Arc<JavaVM>> {
    unsafe { JAVA_VM.clone() }
}

/// Attach current thread to JVM
pub fn attach_current_thread() -> Option<JNIEnv<'static>> {
    get_java_vm().and_then(|vm| {
        vm.attach_current_thread().ok()
    })
}