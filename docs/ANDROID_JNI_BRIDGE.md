# Android JNI Bridge Documentation

## Overview

The Runetika Android JNI bridge provides a robust, type-safe interface between Rust/Bevy and Android/Kotlin. This enables the game to run natively on Android devices while maintaining full access to platform-specific features.

## Architecture

### Layer Structure

```
┌─────────────────────────────────────┐
│     Android UI (Kotlin/Java)        │
├─────────────────────────────────────┤
│      JNI Bridge (Type-Safe)         │
├─────────────────────────────────────┤
│    Rust/Bevy Game Engine Core       │
├─────────────────────────────────────┤
│     Android NDK / Hardware          │
└─────────────────────────────────────┘
```

### Components

#### 1. JNI Bridge Core (`jni_bridge.rs`)
- **Purpose**: Main JNI interface with exported functions
- **Features**:
  - Thread-safe initialization with `Once` guard
  - Global JavaVM reference management
  - Exception handling and error propagation
  - Panic-safe function boundaries

#### 2. Event Handler (`event_handler.rs`)
- **Purpose**: Manages Android input events
- **Handles**:
  - Touch events (multi-touch support)
  - Sensor data (accelerometer, gyroscope, etc.)
  - Android Intents
- **Design**: Lock-free queue with bounded size

#### 3. Surface Renderer (`surface_renderer.rs`)
- **Purpose**: Manages rendering to Android Surface/SurfaceView
- **Features**:
  - Surface lifecycle management
  - GPU context binding
  - Frame presentation

#### 4. Lifecycle Manager (`lifecycle.rs`)
- **Purpose**: Handles Android activity lifecycle
- **States**: Created, Started, Resumed, Paused, Stopped, Destroyed
- **Features**: Automatic resource management based on lifecycle

#### 5. Asset Loader (`asset_loader.rs`)
- **Purpose**: Loads assets from APK
- **Features**:
  - Direct APK asset access
  - Cached loading
  - Memory-mapped files support

#### 6. Logging Bridge (`logging.rs`)
- **Purpose**: Integrates with Android Logcat
- **Features**:
  - Log level mapping
  - Structured logging
  - Performance metrics

#### 7. Memory Manager (`memory.rs`)
- **Purpose**: Safe memory management across JVM boundaries
- **Features**:
  - Global reference tracking
  - Automatic cleanup
  - Memory leak prevention

## API Reference

### Core Functions

```kotlin
// Initialize the Bevy engine
fun initBevy(assetPath: String, cachePath: String): Long

// Update game logic (called each frame)
fun updateBevy(deltaTime: Float): Boolean

// Render frame to surface
fun renderBevy(surface: Surface): Boolean

// Shutdown engine and cleanup
fun shutdownBevy(): Boolean
```

### Input Handling

```kotlin
// Send touch event
fun sendTouchEvent(x: Float, y: Float, action: Int, pointerId: Int): Boolean

// Send sensor data
fun sendSensorData(type: Int, values: FloatArray): Boolean
```

### Lifecycle Management

```kotlin
// Handle Android lifecycle events
fun onLifecycleEvent(event: Int): Boolean
```

### Asset Management

```kotlin
// Load asset from APK
fun loadAsset(path: String): ByteArray?
```

### Performance Monitoring

```kotlin
// Get current FPS
fun getCurrentFps(): Float

// Get memory usage in bytes
fun getMemoryUsage(): Long
```

## Memory Management Guidelines

### JNI Reference Types

1. **Local References**
   - Automatically released when JNI function returns
   - Limited to 512 per function call
   - Use `LocalRefGuard` for RAII pattern

2. **Global References**
   - Persist across JNI calls
   - Must be explicitly deleted
   - Managed by `JniMemoryManager`

### Best Practices

1. **Always use RAII guards** for automatic cleanup
2. **Minimize global references** - use only for long-lived objects
3. **Release arrays immediately** after use
4. **Check for null** before dereferencing Java objects
5. **Handle exceptions** at JNI boundaries

### Memory Leak Prevention

```rust
// Good: Using guard for automatic cleanup
let guard = LocalRefGuard::new(&env, obj);
// Object automatically released when guard drops

// Good: Explicit global reference management
let id = JniMemoryManager::create_global_ref(&env, obj)?;
// ... use reference ...
JniMemoryManager::delete_global_ref(id)?;
```

## Build Configuration

### Gradle Setup

```kotlin
// In android/build.gradle.kts
android {
    defaultConfig {
        ndk {
            abiFilters += listOf("armeabi-v7a", "arm64-v8a", "x86", "x86_64")
        }
    }
}

cargo {
    module = "../"
    libname = "runetika"
    targets = listOf("arm", "arm64", "x86", "x86_64")
    profile = "release"
}
```

### Rust Configuration

```toml
# In Cargo.toml
[lib]
name = "runetika"
crate-type = ["cdylib", "rlib"]

[target.'cfg(target_os = "android")'.dependencies]
jni = "0.21"
android_logger = "0.14"
ndk = "0.9"
```

## Building for Android

### Prerequisites

1. Install Android SDK and NDK
2. Install Rust Android targets:
```bash
rustup target add aarch64-linux-android
rustup target add armv7-linux-androideabi
rustup target add i686-linux-android
rustup target add x86_64-linux-android
```

3. Set environment variables:
```bash
export ANDROID_HOME=/path/to/android-sdk
export NDK_HOME=$ANDROID_HOME/ndk/25.2.9519653
```

### Build Process

1. **Build Rust library**:
```bash
cargo build --target aarch64-linux-android --release
```

2. **Copy to JNI libs**:
```bash
cp target/aarch64-linux-android/release/librunetika.so \
   android/src/main/jniLibs/arm64-v8a/
```

3. **Build Android app**:
```bash
cd android
./gradlew assembleRelease
```

## Thread Safety

### Concurrency Model

- **Main Thread**: Android UI and lifecycle events
- **Render Thread**: Bevy rendering pipeline
- **Game Thread**: Game logic updates
- **JNI Thread**: Bridging calls

### Synchronization

1. **Event Queue**: Lock-free bounded queue for events
2. **State Management**: Atomic operations for state flags
3. **Resource Access**: Mutex-protected shared resources

## Performance Optimizations

### JNI Call Overhead

- **Batch operations** when possible
- **Cache method IDs** for repeated calls
- **Use direct buffers** for large data transfers
- **Minimize string conversions**

### Memory Optimizations

- **Pool objects** to reduce allocations
- **Use primitive arrays** instead of object arrays
- **Release resources** as soon as possible
- **Profile memory usage** with Android Studio

### Rendering Optimizations

- **Double buffering** for smooth rendering
- **Hardware acceleration** via Vulkan/OpenGL ES
- **Texture atlasing** to reduce draw calls
- **Culling** off-screen objects

## Error Handling

### Rust Side

```rust
// Catch panics at JNI boundary
let result = std::panic::catch_unwind(|| {
    // Potentially panicking code
});

match result {
    Ok(Ok(value)) => value,
    Ok(Err(e)) => {
        throw_jni_exception(&env, &format!("Error: {}", e));
        default_value
    },
    Err(_) => {
        throw_jni_exception(&env, "Panic occurred");
        default_value
    }
}
```

### Kotlin Side

```kotlin
try {
    engine.initialize()
} catch (e: RuntimeException) {
    Log.e(TAG, "Engine initialization failed", e)
    // Handle error gracefully
}
```

## Testing

### Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_event_queue() {
        // Test event queue functionality
    }
}
```

### Integration Tests

```kotlin
@Test
fun testEngineInitialization() {
    val engine = RunetikaEngine(context)
    assertTrue(engine.initialize())
    engine.shutdown()
}
```

## Debugging

### Logcat Integration

```rust
// Rust side
android_logger::init_once(
    android_logger::Config::default()
        .with_min_level(log::Level::Debug)
        .with_tag("Runetika")
);

log::debug!("Debug message from Rust");
```

### Android Studio

1. Set breakpoints in Kotlin code
2. Use LLDB for native debugging
3. Monitor memory with Profiler
4. Track JNI calls with systrace

## Security Considerations

1. **Validate all inputs** from Java/Kotlin
2. **Sanitize file paths** for asset loading
3. **Limit memory allocations** to prevent DoS
4. **Use secure random** for cryptographic operations
5. **Implement permission checks** for sensitive operations

## Platform-Specific Features

### Supported Android Versions

- **Minimum SDK**: 24 (Android 7.0)
- **Target SDK**: 34 (Android 14)
- **Tested on**: Android 7.0 - 14.0

### Hardware Requirements

- **RAM**: Minimum 2GB, Recommended 4GB+
- **Storage**: 100MB for base game
- **GPU**: OpenGL ES 3.0 or Vulkan 1.0

## Troubleshooting

### Common Issues

1. **UnsatisfiedLinkError**: Library not found
   - Solution: Ensure .so files are in correct jniLibs folders

2. **OutOfMemoryError**: Memory exhaustion
   - Solution: Increase heap size, optimize memory usage

3. **Surface not valid**: Rendering errors
   - Solution: Check surface lifecycle, synchronize access

4. **JNI reference table overflow**
   - Solution: Release local references, use global refs sparingly

## Future Enhancements

1. **Vulkan rendering** for better performance
2. **Kotlin Multiplatform** support
3. **Advanced sensor integration** (camera, GPS)
4. **Cloud save** synchronization
5. **Play Services** integration
6. **AR/VR** support via ARCore