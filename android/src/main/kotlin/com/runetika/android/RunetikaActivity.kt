package com.runetika.android

import android.app.Activity
import android.os.Bundle
import android.view.SurfaceView
import android.view.SurfaceHolder
import android.view.MotionEvent
import android.hardware.Sensor
import android.hardware.SensorEvent
import android.hardware.SensorEventListener
import android.hardware.SensorManager
import android.content.Context
import android.util.Log
import kotlinx.coroutines.*

/**
 * Main activity for Runetika game
 * Handles surface rendering and input events
 */
class RunetikaActivity : Activity(), SurfaceHolder.Callback, SensorEventListener {
    companion object {
        private const val TAG = "RunetikaActivity"
        private const val TARGET_FPS = 60
        private const val FRAME_TIME_NANOS = 1_000_000_000L / TARGET_FPS
    }

    private lateinit var engine: RunetikaEngine
    private lateinit var surfaceView: SurfaceView
    private lateinit var sensorManager: SensorManager
    
    private var renderJob: Job? = null
    private val renderScope = CoroutineScope(Dispatchers.Default + SupervisorJob())
    private var isRunning = false
    private var surface: android.view.Surface? = null

    // Sensors
    private var accelerometer: Sensor? = null
    private var gyroscope: Sensor? = null

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        Log.d(TAG, "onCreate")
        
        // Initialize engine
        engine = RunetikaEngine(this)
        if (!engine.initialize()) {
            Log.e(TAG, "Failed to initialize engine")
            finish()
            return
        }
        engine.onLifecycleEvent(LifecycleEvent.CREATED)
        
        // Setup surface view
        surfaceView = SurfaceView(this)
        surfaceView.holder.addCallback(this)
        setContentView(surfaceView)
        
        // Initialize sensors
        sensorManager = getSystemService(Context.SENSOR_SERVICE) as SensorManager
        accelerometer = sensorManager.getDefaultSensor(Sensor.TYPE_ACCELEROMETER)
        gyroscope = sensorManager.getDefaultSensor(Sensor.TYPE_GYROSCOPE)
    }

    override fun surfaceCreated(holder: SurfaceHolder) {
        Log.d(TAG, "surfaceCreated")
        surface = holder.surface
        startRenderLoop()
    }

    override fun surfaceChanged(holder: SurfaceHolder, format: Int, width: Int, height: Int) {
        Log.d(TAG, "surfaceChanged: ${width}x${height}")
        // Handle surface size changes
    }

    override fun surfaceDestroyed(holder: SurfaceHolder) {
        Log.d(TAG, "surfaceDestroyed")
        stopRenderLoop()
        surface = null
    }

    private fun startRenderLoop() {
        if (isRunning) return
        
        isRunning = true
        renderJob = renderScope.launch {
            var lastFrameTime = System.nanoTime()
            
            while (isRunning && isActive) {
                val currentTime = System.nanoTime()
                val deltaTime = currentTime - lastFrameTime
                
                surface?.let { surf ->
                    try {
                        // Update game logic
                        engine.update()
                        
                        // Render frame
                        engine.render(surf)
                        
                        // Calculate sleep time to maintain target FPS
                        val sleepTime = FRAME_TIME_NANOS - (System.nanoTime() - currentTime)
                        if (sleepTime > 0) {
                            delay(sleepTime / 1_000_000) // Convert to milliseconds
                        }
                    } catch (e: Exception) {
                        Log.e(TAG, "Error in render loop", e)
                    }
                }
                
                lastFrameTime = currentTime
            }
        }
    }

    private fun stopRenderLoop() {
        isRunning = false
        runBlocking {
            renderJob?.cancelAndJoin()
        }
        renderJob = null
    }

    override fun onTouchEvent(event: MotionEvent): Boolean {
        return engine.handleTouch(event) || super.onTouchEvent(event)
    }

    override fun onSensorChanged(event: SensorEvent) {
        when (event.sensor.type) {
            Sensor.TYPE_ACCELEROMETER,
            Sensor.TYPE_GYROSCOPE -> {
                engine.handleSensor(event.sensor, event.values)
            }
        }
    }

    override fun onAccuracyChanged(sensor: Sensor, accuracy: Int) {
        // Handle sensor accuracy changes if needed
    }

    override fun onStart() {
        super.onStart()
        Log.d(TAG, "onStart")
        engine.onLifecycleEvent(LifecycleEvent.STARTED)
    }

    override fun onResume() {
        super.onResume()
        Log.d(TAG, "onResume")
        engine.onLifecycleEvent(LifecycleEvent.RESUMED)
        
        // Register sensor listeners
        accelerometer?.let {
            sensorManager.registerListener(this, it, SensorManager.SENSOR_DELAY_GAME)
        }
        gyroscope?.let {
            sensorManager.registerListener(this, it, SensorManager.SENSOR_DELAY_GAME)
        }
    }

    override fun onPause() {
        super.onPause()
        Log.d(TAG, "onPause")
        engine.onLifecycleEvent(LifecycleEvent.PAUSED)
        
        // Unregister sensor listeners
        sensorManager.unregisterListener(this)
    }

    override fun onStop() {
        super.onStop()
        Log.d(TAG, "onStop")
        engine.onLifecycleEvent(LifecycleEvent.STOPPED)
    }

    override fun onDestroy() {
        super.onDestroy()
        Log.d(TAG, "onDestroy")
        
        stopRenderLoop()
        renderScope.cancel()
        
        engine.onLifecycleEvent(LifecycleEvent.DESTROYED)
        engine.shutdown()
    }
}