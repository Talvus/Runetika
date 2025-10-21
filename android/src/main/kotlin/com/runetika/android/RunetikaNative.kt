package com.runetika.android

import android.view.Surface
import android.content.Context
import android.view.MotionEvent
import android.hardware.Sensor
import android.content.Intent
import androidx.annotation.Keep

/**
 * Native interface for Runetika game engine
 * Provides JNI bridge to Rust/Bevy implementation
 */
@Keep
object RunetikaNative {
    init {
        System.loadLibrary("runetika")
    }

    // Core Engine Functions
    @JvmStatic
    external fun initBevy(assetPath: String, cachePath: String): Long

    @JvmStatic
    external fun updateBevy(deltaTime: Float): Boolean

    @JvmStatic
    external fun renderBevy(surface: Surface): Boolean

    @JvmStatic
    external fun shutdownBevy(): Boolean

    // Input Handling
    @JvmStatic
    external fun sendTouchEvent(x: Float, y: Float, action: Int, pointerId: Int): Boolean

    @JvmStatic
    external fun sendSensorData(type: Int, values: FloatArray): Boolean

    // Lifecycle Management
    @JvmStatic
    external fun onLifecycleEvent(event: Int): Boolean

    // Asset Management
    @JvmStatic
    external fun loadAsset(path: String): ByteArray?

    // Performance Monitoring
    @JvmStatic
    external fun getCurrentFps(): Float

    @JvmStatic
    external fun getMemoryUsage(): Long
}

/**
 * High-level wrapper for Runetika engine
 * Provides convenient Kotlin API with type safety
 */
@Keep
class RunetikaEngine(private val context: Context) {
    private var engineHandle: Long = 0
    private var isInitialized = false
    private var lastFrameTime = System.nanoTime()

    /**
     * Initialize the game engine
     */
    fun initialize(): Boolean {
        if (isInitialized) return true

        val assetPath = context.filesDir.absolutePath
        val cachePath = context.cacheDir.absolutePath

        engineHandle = RunetikaNative.initBevy(assetPath, cachePath)
        isInitialized = engineHandle != 0L
        return isInitialized
    }

    /**
     * Update game logic
     */
    fun update(): Boolean {
        if (!isInitialized) return false

        val currentTime = System.nanoTime()
        val deltaTime = (currentTime - lastFrameTime) / 1_000_000_000f
        lastFrameTime = currentTime

        return RunetikaNative.updateBevy(deltaTime)
    }

    /**
     * Render frame to surface
     */
    fun render(surface: Surface): Boolean {
        if (!isInitialized) return false
        return RunetikaNative.renderBevy(surface)
    }

    /**
     * Handle touch events
     */
    fun handleTouch(event: MotionEvent): Boolean {
        if (!isInitialized) return false

        val action = event.actionMasked
        val pointerIndex = event.actionIndex
        val pointerId = event.getPointerId(pointerIndex)
        val x = event.getX(pointerIndex)
        val y = event.getY(pointerIndex)

        return RunetikaNative.sendTouchEvent(x, y, action, pointerId)
    }

    /**
     * Handle sensor data
     */
    fun handleSensor(sensor: Sensor, values: FloatArray): Boolean {
        if (!isInitialized) return false
        return RunetikaNative.sendSensorData(sensor.type, values)
    }

    /**
     * Handle lifecycle events
     */
    fun onLifecycleEvent(event: LifecycleEvent): Boolean {
        if (!isInitialized && event != LifecycleEvent.CREATED) return false
        return RunetikaNative.onLifecycleEvent(event.ordinal)
    }

    /**
     * Shutdown the engine
     */
    fun shutdown() {
        if (isInitialized) {
            RunetikaNative.shutdownBevy()
            isInitialized = false
            engineHandle = 0
        }
    }

    /**
     * Get current FPS
     */
    fun getFps(): Float = RunetikaNative.getCurrentFps()

    /**
     * Get memory usage in bytes
     */
    fun getMemoryUsage(): Long = RunetikaNative.getMemoryUsage()
}

/**
 * Android lifecycle events
 */
@Keep
enum class LifecycleEvent {
    CREATED,
    STARTED,
    RESUMED,
    PAUSED,
    STOPPED,
    DESTROYED
}