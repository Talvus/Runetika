# Runetika iOS FFI Bridge

This directory contains the Foreign Function Interface (FFI) bridge for integrating Runetika with iOS applications using Swift.

## Architecture Overview

The FFI bridge provides a C-compatible API that Swift can call to interact with the Rust/Bevy game engine. It handles:

- **Memory Management**: Safe allocation and deallocation across language boundaries
- **Event System**: iOS events (touch, accelerometer, lifecycle) → Bevy
- **Thread Safety**: Concurrent calls from iOS main and render threads
- **Error Handling**: Comprehensive error reporting with callbacks
- **Performance Monitoring**: Real-time metrics and profiling

## Building for iOS

### Prerequisites

1. Install Rust iOS targets:
```bash
rustup target add aarch64-apple-ios
rustup target add aarch64-apple-ios-sim
rustup target add x86_64-apple-ios
```

2. Install Xcode and command line tools:
```bash
xcode-select --install
```

### Build Process

Run the build script:
```bash
./ios/build_ios.sh
```

This creates:
- `librunetika_device.a` - iOS device library (ARM64)
- `librunetika_simulator.a` - iOS simulator universal library
- `Runetika.xcframework` - XCFramework for all platforms
- `runetika.h` - C header file

## Swift Integration

### 1. Add to Xcode Project

1. Drag `Runetika.xcframework` into your Xcode project
2. Ensure "Copy items if needed" is checked
3. Add to your app target

### 2. Configure Bridging Header

Create or update your bridging header (`YourApp-Bridging-Header.h`):

```c
#import "runetika.h"
```

### 3. Swift Wrapper Example

```swift
import Foundation
import UIKit

class RunetikaEngine {
    private var engine: OpaquePointer?
    private var isInitialized = false
    
    init() {
        setupEngine()
    }
    
    deinit {
        shutdown()
    }
    
    private func setupEngine() {
        var config = RunetikaConfig()
        config.window_width = Float(UIScreen.main.bounds.width)
        config.window_height = Float(UIScreen.main.bounds.height)
        config.scale_factor = Float(UIScreen.main.scale)
        config.target_fps = 60
        config.debug_mode = false
        config.enable_profiling = true
        config.max_touches = 10
        config.audio_enabled = true
        config.use_metal = true
        
        // Set error callback
        let errorCallback: RunetikaErrorCallback = { errorCode, message in
            if let msg = message {
                let swiftString = String(cString: msg)
                print("Runetika Error (\(errorCode)): \(swiftString)")
            }
        }
        
        engine = runetika_init(&config, errorCallback)
        isInitialized = engine != nil
        
        if isInitialized {
            // Set up additional callbacks
            setupCallbacks()
        }
    }
    
    private func setupCallbacks() {
        // Log callback
        let logCallback: RunetikaLogCallback = { level, message in
            if let msg = message {
                let swiftString = String(cString: msg)
                switch level {
                case RUNETIKA_LOG_DEBUG:
                    print("🔍 [DEBUG] \(swiftString)")
                case RUNETIKA_LOG_INFO:
                    print("ℹ️ [INFO] \(swiftString)")
                case RUNETIKA_LOG_ERROR:
                    print("❌ [ERROR] \(swiftString)")
                default:
                    print("\(swiftString)")
                }
            }
        }
        
        runetika_set_log_callback(engine, logCallback)
    }
    
    func update(deltaTime: Float) {
        guard isInitialized, let engine = engine else { return }
        
        let result = runetika_update(engine, deltaTime)
        if result != RUNETIKA_SUCCESS {
            print("Update failed with error: \(result)")
        }
    }
    
    func render(framebuffer: UInt32, width: UInt32, height: UInt32) {
        guard isInitialized, let engine = engine else { return }
        
        let result = runetika_render(engine, framebuffer, width, height)
        if result != RUNETIKA_SUCCESS {
            print("Render failed with error: \(result)")
        }
    }
    
    func sendTouch(id: UInt64, phase: UITouch.Phase, location: CGPoint, force: CGFloat) {
        guard isInitialized, let engine = engine else { return }
        
        let runetikaPhase: UInt32
        switch phase {
        case .began:
            runetikaPhase = RUNETIKA_TOUCH_BEGAN
        case .moved:
            runetikaPhase = RUNETIKA_TOUCH_MOVED
        case .stationary:
            runetikaPhase = RUNETIKA_TOUCH_STATIONARY
        case .ended:
            runetikaPhase = RUNETIKA_TOUCH_ENDED
        case .cancelled:
            runetikaPhase = RUNETIKA_TOUCH_CANCELLED
        default:
            runetikaPhase = RUNETIKA_TOUCH_CANCELLED
        }
        
        runetika_send_touch(
            engine,
            id,
            runetikaPhase,
            Float(location.x),
            Float(location.y),
            Float(force)
        )
    }
    
    func sendAccelerometer(x: Float, y: Float, z: Float) {
        guard isInitialized, let engine = engine else { return }
        runetika_send_accelerometer(engine, x, y, z)
    }
    
    func sendLifecycleEvent(_ event: RunetikaLifecycleEvent) {
        guard isInitialized, let engine = engine else { return }
        runetika_send_lifecycle_event(engine, event.rawValue)
    }
    
    func shutdown() {
        guard isInitialized, let engine = engine else { return }
        
        runetika_shutdown(engine)
        self.engine = nil
        isInitialized = false
    }
}
```

### 4. Metal View Integration

```swift
import MetalKit

class GameViewController: UIViewController {
    var engine: RunetikaEngine!
    var metalView: MTKView!
    var displayLink: CADisplayLink!
    
    override func viewDidLoad() {
        super.viewDidLoad()
        
        // Set up Metal view
        metalView = MTKView(frame: view.bounds)
        metalView.device = MTLCreateSystemDefaultDevice()
        metalView.colorPixelFormat = .bgra8Unorm
        metalView.depthStencilPixelFormat = .depth32Float
        view.addSubview(metalView)
        
        // Initialize engine
        engine = RunetikaEngine()
        
        // Set up display link for updates
        displayLink = CADisplayLink(target: self, selector: #selector(update))
        displayLink.add(to: .main, forMode: .default)
    }
    
    @objc func update() {
        let deltaTime = Float(displayLink.targetTimestamp - displayLink.timestamp)
        engine.update(deltaTime: deltaTime)
        
        // Render
        if let drawable = metalView.currentDrawable {
            engine.render(
                framebuffer: 0, // Metal doesn't use framebuffer IDs
                width: UInt32(metalView.bounds.width * metalView.contentScaleFactor),
                height: UInt32(metalView.bounds.height * metalView.contentScaleFactor)
            )
            drawable.present()
        }
    }
    
    override func touchesBegan(_ touches: Set<UITouch>, with event: UIEvent?) {
        for touch in touches {
            let location = touch.location(in: metalView)
            engine.sendTouch(
                id: UInt64(touch.hash),
                phase: touch.phase,
                location: location,
                force: touch.force
            )
        }
    }
    
    // Implement other touch methods similarly...
}
```

## Memory Management Guidelines

### Ownership Rules

1. **Rust owns engine state**: The engine handle is owned by Rust and borrowed by Swift
2. **Swift retains references**: Use `runetika_retain()` and `runetika_release()` for reference counting
3. **Explicit deallocation**: Always call `runetika_shutdown()` before releasing the engine

### Memory Transfer Patterns

```swift
// Allocating memory for Rust
let buffer = runetika_alloc(1024)
defer { runetika_free(buffer, 1024) }

// Creating buffers
var data = [UInt8](repeating: 0, count: 100)
let buffer = runetika_buffer_create(&data, data.count)
defer { runetika_buffer_free(buffer) }
```

## Thread Safety

The FFI bridge is designed for concurrent access:

- **Update thread**: Call `runetika_update()` from your game loop thread
- **Render thread**: Call `runetika_render()` from the Metal/OpenGL thread
- **Event thread**: Send events from any thread (internally synchronized)

## Error Handling

Check return codes and use callbacks:

```swift
let result = runetika_update(engine, deltaTime)
switch result {
case RUNETIKA_SUCCESS:
    // Success
    break
case RUNETIKA_ERROR_NULL_HANDLE:
    print("Engine not initialized")
case RUNETIKA_ERROR_LOCK_FAILED:
    print("Thread contention")
default:
    if let errorStr = runetika_error_string(result) {
        print("Error: \(String(cString: errorStr))")
    }
}
```

## Performance Monitoring

Get real-time metrics:

```swift
var metrics = RunetikaPerformanceMetrics()
if runetika_get_performance_metrics(engine, &metrics) == RUNETIKA_SUCCESS {
    print("FPS: \(metrics.fps)")
    print("Frame time: \(metrics.frame_time_ms)ms")
    print("Memory: \(metrics.memory.allocated_bytes) bytes")
}
```

## Troubleshooting

### Common Issues

1. **Linking errors**: Ensure you're linking against:
   - Metal.framework
   - CoreMotion.framework
   - AVFoundation.framework
   - CoreGraphics.framework

2. **Symbol not found**: Check that the library architecture matches your target:
   ```bash
   lipo -info librunetika.a
   ```

3. **Memory leaks**: Use Instruments to track allocations:
   - All allocations should go through `runetika_alloc/free`
   - Check reference counting with `runetika_ref_count()`

### Debug Mode

Enable debug mode in the config:
```swift
config.debug_mode = true
config.enable_profiling = true
```

This enables:
- Debug rendering overlays
- Performance metrics
- Detailed logging
- Touch visualization

## API Reference

See `runetika.h` for the complete C API documentation.

## Example iOS App

A complete example iOS app is available in `ios/Example/` (to be added).

## License

Same as the main Runetika project.