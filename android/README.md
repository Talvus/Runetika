# Runetika Android Integration

This directory contains the Android-specific code for running Runetika on Android devices using JNI (Java Native Interface) to bridge between Kotlin/Java and Rust/Bevy.

## Architecture Overview

```
Kotlin/Java (Android UI) ←→ JNI Bridge ←→ Rust/Bevy (Game Engine)
```

## Project Structure

```
android/
├── build.gradle.kts          # Gradle build configuration
├── settings.gradle.kts        # Gradle settings
├── src/
│   ├── main/
│   │   ├── AndroidManifest.xml
│   │   ├── kotlin/
│   │   │   └── com/runetika/android/
│   │   │       ├── RunetikaNative.kt    # JNI declarations
│   │   │       ├── RunetikaEngine.kt    # High-level API
│   │   │       └── RunetikaActivity.kt  # Main activity
│   │   └── jniLibs/           # Native libraries (generated)
│   │       ├── arm64-v8a/
│   │       ├── armeabi-v7a/
│   │       ├── x86/
│   │       └── x86_64/
│   └── test/                  # Unit tests
└── README.md
```

## Prerequisites

1. **Android SDK** (API Level 24+)
2. **Android NDK** (version 25.2.9519653 or later)
3. **Rust** with Android targets:
   ```bash
   rustup target add aarch64-linux-android
   rustup target add armv7-linux-androideabi
   rustup target add i686-linux-android
   rustup target add x86_64-linux-android
   ```
4. **Android Studio** (recommended for development)

## Building

### Quick Build

From the project root:

```bash
./build_android.sh
```

This script will:
1. Check prerequisites
2. Install Rust Android targets
3. Build native libraries for all architectures
4. Copy libraries to JNI folder
5. Strip debug symbols

### Manual Build

1. **Set environment variables**:
   ```bash
   export ANDROID_HOME=/path/to/android-sdk
   export NDK_HOME=$ANDROID_HOME/ndk/25.2.9519653
   ```

2. **Build Rust library**:
   ```bash
   cargo build --target aarch64-linux-android --release --lib
   ```

3. **Build Android app**:
   ```bash
   cd android
   ./gradlew assembleDebug
   ```

## Running

### On Emulator

```bash
cd android
./gradlew installDebug
adb shell am start -n com.runetika.android/.RunetikaActivity
```

### On Device

1. Enable USB debugging on your Android device
2. Connect device via USB
3. Run:
   ```bash
   cd android
   ./gradlew installDebug
   ```

## Development

### Adding New JNI Functions

1. **Rust side** (in `src/android/jni_bridge.rs`):
   ```rust
   #[no_mangle]
   pub extern "system" fn Java_com_runetika_android_RunetikaNative_myFunction(
       env: JNIEnv,
       _class: JClass,
       param: jint,
   ) -> jboolean {
       // Implementation
       1 // true
   }
   ```

2. **Kotlin side** (in `RunetikaNative.kt`):
   ```kotlin
   @JvmStatic
   external fun myFunction(param: Int): Boolean
   ```

### Handling Android Events

Events flow from Android → Rust through the event queue:

```kotlin
// Kotlin: Send event
engine.handleTouch(motionEvent)

// Rust: Process event (in Bevy system)
fn process_touch_events(mut events: EventReader<AndroidTouchEvent>) {
    for event in events.iter() {
        // Handle touch
    }
}
```

### Memory Management

- **Local references**: Automatically cleaned up
- **Global references**: Must be explicitly deleted
- **Arrays**: Use `JniArray` wrapper for safe access
- **Strings**: Convert at boundaries, minimize allocations

## Performance

### Optimization Tips

1. **Batch JNI calls** to reduce overhead
2. **Use direct ByteBuffers** for large data transfers
3. **Cache method/field IDs** for repeated access
4. **Profile with Android Studio** Profiler
5. **Monitor frame times** with systrace

### Target Performance

- **FPS**: 60 FPS on mid-range devices
- **Memory**: < 200MB for base game
- **Battery**: < 10% drain per hour
- **Startup**: < 3 seconds cold start

## Debugging

### Logcat

View Rust logs in Android Studio or terminal:

```bash
adb logcat -s Runetika:V
```

### Native Debugging

1. In Android Studio: Run → Edit Configurations
2. Add Native debugging
3. Set breakpoints in Rust code
4. Use LLDB commands in debug console

### Common Issues

| Issue | Solution |
|-------|----------|
| `UnsatisfiedLinkError` | Check library is in correct jniLibs folder |
| `OutOfMemoryError` | Increase heap size, optimize textures |
| Surface errors | Check lifecycle handling |
| Slow performance | Profile with systrace, reduce draw calls |

## Testing

### Unit Tests

```bash
cd android
./gradlew test
```

### Instrumented Tests

```bash
cd android
./gradlew connectedAndroidTest
```

### Performance Testing

```bash
# Start profiling
adb shell am start -n com.runetika.android/.RunetikaActivity \
    --start-profiler /sdcard/runetika.trace

# Stop profiling
adb shell am profile stop com.runetika.android

# Pull trace
adb pull /sdcard/runetika.trace
```

## Release Build

1. **Create signing key**:
   ```bash
   keytool -genkey -v -keystore runetika.keystore \
     -alias runetika -keyalg RSA -keysize 2048 -validity 10000
   ```

2. **Configure signing** in `build.gradle.kts`:
   ```kotlin
   signingConfigs {
       create("release") {
           storeFile = file("runetika.keystore")
           storePassword = "password"
           keyAlias = "runetika"
           keyPassword = "password"
       }
   }
   ```

3. **Build release APK**:
   ```bash
   ./gradlew assembleRelease
   ```

4. **Build AAB for Play Store**:
   ```bash
   ./gradlew bundleRelease
   ```

## Platform Support

### Minimum Requirements

- **Android**: 7.0 (API 24)
- **RAM**: 2GB minimum, 4GB recommended
- **Storage**: 100MB
- **GPU**: OpenGL ES 3.0

### Tested Devices

- Pixel 6/7/8 series
- Samsung Galaxy S20/S21/S22/S23
- OnePlus 9/10/11
- Xiaomi Mi 11/12/13
- Android emulators (x86_64)

## Troubleshooting

### Build Failures

```bash
# Clean build
./gradlew clean
rm -rf ~/.gradle/caches
cargo clean

# Rebuild
./build_android.sh
```

### Runtime Crashes

1. Check logcat for stack traces
2. Verify all .so files are present
3. Test on different architectures
4. Check memory usage

## Contributing

1. Follow existing code style
2. Add tests for new features
3. Update documentation
4. Test on multiple devices
5. Profile performance impact

## License

See main project LICENSE file.

## Support

For issues specific to Android:
- Check [docs/ANDROID_JNI_BRIDGE.md](../docs/ANDROID_JNI_BRIDGE.md)
- File issues with `android` label
- Include device info and logcat output