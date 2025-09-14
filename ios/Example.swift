// Example Swift integration for Runetika iOS FFI Bridge
// This demonstrates how to integrate Runetika into an iOS app

import Foundation
import UIKit
import MetalKit
import CoreMotion

/// Main Runetika engine wrapper for Swift
class RunetikaEngine {
    private var engine: OpaquePointer?
    private var isInitialized = false
    private let motionManager = CMMotionManager()
    
    // MARK: - Initialization
    
    init(width: Float, height: Float, scaleFactor: Float) {
        setupEngine(width: width, height: height, scaleFactor: scaleFactor)
        setupMotionTracking()
    }
    
    deinit {
        shutdown()
    }
    
    private func setupEngine(width: Float, height: Float, scaleFactor: Float) {
        var config = RunetikaConfig()
        config.window_width = width
        config.window_height = height
        config.scale_factor = scaleFactor
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
                print("❌ Runetika Error (\(errorCode)): \(swiftString)")
            }
        }
        
        engine = runetika_init(&config, errorCallback)
        isInitialized = engine != nil
        
        if isInitialized {
            print("✅ Runetika engine initialized successfully")
            setupCallbacks()
        } else {
            print("❌ Failed to initialize Runetika engine")
        }
    }
    
    private func setupCallbacks() {
        guard let engine = engine else { return }
        
        // Log callback
        let logCallback: RunetikaLogCallback = { level, message in
            if let msg = message {
                let swiftString = String(cString: msg)
                switch level {
                case UInt32(RUNETIKA_LOG_DEBUG):
                    print("🔍 [DEBUG] \(swiftString)")
                case UInt32(RUNETIKA_LOG_INFO):
                    print("ℹ️ [INFO] \(swiftString)")
                case UInt32(RUNETIKA_LOG_ERROR):
                    print("❌ [ERROR] \(swiftString)")
                default:
                    print("📝 \(swiftString)")
                }
            }
        }
        
        runetika_set_log_callback(engine, logCallback)
    }
    
    private func setupMotionTracking() {
        // Set up accelerometer
        if motionManager.isAccelerometerAvailable {
            motionManager.accelerometerUpdateInterval = 1.0 / 60.0
            motionManager.startAccelerometerUpdates(to: .main) { [weak self] data, error in
                guard let data = data, let self = self else { return }
                self.sendAccelerometer(
                    x: Float(data.acceleration.x),
                    y: Float(data.acceleration.y),
                    z: Float(data.acceleration.z)
                )
            }
        }
        
        // Set up gyroscope
        if motionManager.isGyroAvailable {
            motionManager.gyroUpdateInterval = 1.0 / 60.0
            motionManager.startGyroUpdates(to: .main) { [weak self] data, error in
                guard let data = data, let self = self else { return }
                self.sendGyroscope(
                    x: Float(data.rotationRate.x),
                    y: Float(data.rotationRate.y),
                    z: Float(data.rotationRate.z)
                )
            }
        }
    }
    
    // MARK: - Game Loop
    
    func update(deltaTime: Float) {
        guard isInitialized, let engine = engine else { return }
        
        let result = runetika_update(engine, deltaTime)
        if result != RUNETIKA_SUCCESS {
            if let errorStr = runetika_error_string(result) {
                print("Update failed: \(String(cString: errorStr))")
            }
        }
    }
    
    func render(framebuffer: UInt32, width: UInt32, height: UInt32) {
        guard isInitialized, let engine = engine else { return }
        
        let result = runetika_render(engine, framebuffer, width, height)
        if result != RUNETIKA_SUCCESS {
            if let errorStr = runetika_error_string(result) {
                print("Render failed: \(String(cString: errorStr))")
            }
        }
    }
    
    // MARK: - Input Handling
    
    func sendTouch(id: UInt64, phase: UITouch.Phase, location: CGPoint, force: CGFloat) {
        guard isInitialized, let engine = engine else { return }
        
        let runetikaPhase: UInt32
        switch phase {
        case .began:
            runetikaPhase = UInt32(RUNETIKA_TOUCH_BEGAN)
        case .moved:
            runetikaPhase = UInt32(RUNETIKA_TOUCH_MOVED)
        case .stationary:
            runetikaPhase = UInt32(RUNETIKA_TOUCH_STATIONARY)
        case .ended:
            runetikaPhase = UInt32(RUNETIKA_TOUCH_ENDED)
        case .cancelled:
            runetikaPhase = UInt32(RUNETIKA_TOUCH_CANCELLED)
        default:
            runetikaPhase = UInt32(RUNETIKA_TOUCH_CANCELLED)
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
    
    func sendBatchTouches(_ touches: Set<UITouch>, in view: UIView) {
        guard isInitialized, let engine = engine else { return }
        
        var touchEvents: [RunetikaTouchEvent] = []
        
        for touch in touches {
            let location = touch.location(in: view)
            
            var event = RunetikaTouchEvent()
            event.id = UInt64(touch.hash)
            event.phase = touchPhaseToRunetika(touch.phase)
            event.x = Float(location.x)
            event.y = Float(location.y)
            event.force = Float(touch.force)
            
            // Set timestamp
            let now = Date()
            event.timestamp_sec = UInt64(now.timeIntervalSince1970)
            event.timestamp_nsec = UInt32((now.timeIntervalSince1970.truncatingRemainder(dividingBy: 1)) * 1_000_000_000)
            
            touchEvents.append(event)
        }
        
        touchEvents.withUnsafeBufferPointer { buffer in
            runetika_send_touches_batch(engine, buffer.baseAddress, touchEvents.count)
        }
    }
    
    private func touchPhaseToRunetika(_ phase: UITouch.Phase) -> UInt32 {
        switch phase {
        case .began: return UInt32(RUNETIKA_TOUCH_BEGAN)
        case .moved: return UInt32(RUNETIKA_TOUCH_MOVED)
        case .stationary: return UInt32(RUNETIKA_TOUCH_STATIONARY)
        case .ended: return UInt32(RUNETIKA_TOUCH_ENDED)
        case .cancelled: return UInt32(RUNETIKA_TOUCH_CANCELLED)
        default: return UInt32(RUNETIKA_TOUCH_CANCELLED)
        }
    }
    
    func sendAccelerometer(x: Float, y: Float, z: Float) {
        guard isInitialized, let engine = engine else { return }
        runetika_send_accelerometer(engine, x, y, z)
    }
    
    func sendGyroscope(x: Float, y: Float, z: Float) {
        guard isInitialized, let engine = engine else { return }
        runetika_send_gyroscope(engine, x, y, z)
    }
    
    // MARK: - Lifecycle
    
    func sendLifecycleEvent(_ event: LifecycleEvent) {
        guard isInitialized, let engine = engine else { return }
        runetika_send_lifecycle_event(engine, event.rawValue)
    }
    
    func shutdown() {
        guard isInitialized, let engine = engine else { return }
        
        motionManager.stopAccelerometerUpdates()
        motionManager.stopGyroUpdates()
        
        runetika_shutdown(engine)
        self.engine = nil
        isInitialized = false
        
        print("✅ Runetika engine shut down")
    }
    
    // MARK: - Performance Monitoring
    
    func getPerformanceMetrics() -> PerformanceMetrics? {
        guard isInitialized, let engine = engine else { return nil }
        
        var metrics = RunetikaPerformanceMetrics()
        let result = runetika_get_performance_metrics(engine, &metrics)
        
        if result == RUNETIKA_SUCCESS {
            return PerformanceMetrics(
                fps: metrics.fps,
                frameTimeMs: metrics.frame_time_ms,
                updateTimeMs: metrics.update_time_ms,
                renderTimeMs: metrics.render_time_ms,
                drawCalls: metrics.draw_calls,
                entityCount: metrics.entity_count,
                memoryMB: Double(metrics.memory.allocated_bytes) / 1_048_576.0
            )
        }
        
        return nil
    }
}

// MARK: - Supporting Types

enum LifecycleEvent: UInt32 {
    case willEnterForeground = 0
    case didBecomeActive = 1
    case willResignActive = 2
    case didEnterBackground = 3
    case willTerminate = 4
    case memoryWarning = 5
}

struct PerformanceMetrics {
    let fps: Float
    let frameTimeMs: Float
    let updateTimeMs: Float
    let renderTimeMs: Float
    let drawCalls: UInt32
    let entityCount: UInt32
    let memoryMB: Double
}

// MARK: - View Controller

class GameViewController: UIViewController {
    var engine: RunetikaEngine!
    var metalView: MTKView!
    var displayLink: CADisplayLink!
    var lastTimestamp: CFTimeInterval = 0
    
    override func viewDidLoad() {
        super.viewDidLoad()
        
        setupMetalView()
        setupEngine()
        setupDisplayLink()
        setupLifecycleObservers()
    }
    
    private func setupMetalView() {
        metalView = MTKView(frame: view.bounds)
        metalView.device = MTLCreateSystemDefaultDevice()
        metalView.colorPixelFormat = .bgra8Unorm
        metalView.depthStencilPixelFormat = .depth32Float
        metalView.autoresizingMask = [.flexibleWidth, .flexibleHeight]
        view.addSubview(metalView)
    }
    
    private func setupEngine() {
        let scale = UIScreen.main.scale
        engine = RunetikaEngine(
            width: Float(view.bounds.width),
            height: Float(view.bounds.height),
            scaleFactor: Float(scale)
        )
    }
    
    private func setupDisplayLink() {
        displayLink = CADisplayLink(target: self, selector: #selector(gameLoop))
        displayLink.add(to: .main, forMode: .default)
    }
    
    private func setupLifecycleObservers() {
        NotificationCenter.default.addObserver(
            self,
            selector: #selector(appWillEnterForeground),
            name: UIApplication.willEnterForegroundNotification,
            object: nil
        )
        
        NotificationCenter.default.addObserver(
            self,
            selector: #selector(appDidBecomeActive),
            name: UIApplication.didBecomeActiveNotification,
            object: nil
        )
        
        NotificationCenter.default.addObserver(
            self,
            selector: #selector(appWillResignActive),
            name: UIApplication.willResignActiveNotification,
            object: nil
        )
        
        NotificationCenter.default.addObserver(
            self,
            selector: #selector(appDidEnterBackground),
            name: UIApplication.didEnterBackgroundNotification,
            object: nil
        )
    }
    
    @objc private func gameLoop() {
        let currentTimestamp = displayLink.timestamp
        let deltaTime = lastTimestamp > 0 ? Float(currentTimestamp - lastTimestamp) : 1.0/60.0
        lastTimestamp = currentTimestamp
        
        // Update game logic
        engine.update(deltaTime: deltaTime)
        
        // Render
        if let drawable = metalView.currentDrawable {
            let width = UInt32(metalView.drawableSize.width)
            let height = UInt32(metalView.drawableSize.height)
            
            engine.render(framebuffer: 0, width: width, height: height)
            
            drawable.present()
        }
        
        // Display performance metrics periodically
        if Int(currentTimestamp) % 60 == 0 {
            if let metrics = engine.getPerformanceMetrics() {
                print("📊 FPS: \(metrics.fps), Memory: \(String(format: "%.2f", metrics.memoryMB))MB")
            }
        }
    }
    
    // MARK: - Touch Handling
    
    override func touchesBegan(_ touches: Set<UITouch>, with event: UIEvent?) {
        engine.sendBatchTouches(touches, in: metalView)
    }
    
    override func touchesMoved(_ touches: Set<UITouch>, with event: UIEvent?) {
        engine.sendBatchTouches(touches, in: metalView)
    }
    
    override func touchesEnded(_ touches: Set<UITouch>, with event: UIEvent?) {
        engine.sendBatchTouches(touches, in: metalView)
    }
    
    override func touchesCancelled(_ touches: Set<UITouch>, with event: UIEvent?) {
        engine.sendBatchTouches(touches, in: metalView)
    }
    
    // MARK: - Lifecycle Events
    
    @objc private func appWillEnterForeground() {
        engine.sendLifecycleEvent(.willEnterForeground)
    }
    
    @objc private func appDidBecomeActive() {
        engine.sendLifecycleEvent(.didBecomeActive)
    }
    
    @objc private func appWillResignActive() {
        engine.sendLifecycleEvent(.willResignActive)
    }
    
    @objc private func appDidEnterBackground() {
        engine.sendLifecycleEvent(.didEnterBackground)
    }
    
    override func didReceiveMemoryWarning() {
        super.didReceiveMemoryWarning()
        engine.sendLifecycleEvent(.memoryWarning)
    }
    
    deinit {
        displayLink?.invalidate()
        engine?.shutdown()
    }
}