/// Kotlin Interface Definitions
/// Provides type-safe Kotlin class signatures for code generation

use std::fmt::Write;

/// Generate Kotlin wrapper classes
pub fn generate_kotlin_wrapper() -> String {
    let mut output = String::new();
    
    // Package declaration
    writeln!(&mut output, "package com.runetika.android\n").unwrap();
    
    // Imports
    writeln!(&mut output, "import android.view.Surface").unwrap();
    writeln!(&mut output, "import android.content.Context").unwrap();
    writeln!(&mut output, "import android.view.MotionEvent").unwrap();
    writeln!(&mut output, "import android.hardware.Sensor").unwrap();
    writeln!(&mut output, "import android.content.Intent").unwrap();
    writeln!(&mut output, "import androidx.annotation.Keep\n").unwrap();
    
    // Main native interface class
    writeln!(&mut output, "/**").unwrap();
    writeln!(&mut output, " * Native interface for Runetika game engine").unwrap();
    writeln!(&mut output, " * Provides JNI bridge to Rust/Bevy implementation").unwrap();
    writeln!(&mut output, " */").unwrap();
    writeln!(&mut output, "@Keep").unwrap();
    writeln!(&mut output, "object RuneikaNative {{").unwrap();
    writeln!(&mut output, "    init {{").unwrap();
    writeln!(&mut output, "        System.loadLibrary(\"runetika\")").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    // Core engine functions
    writeln!(&mut output, "    // Core Engine Functions").unwrap();
    writeln!(&mut output, "    @JvmStatic").unwrap();
    writeln!(&mut output, "    external fun initBevy(assetPath: String, cachePath: String): Long\n").unwrap();
    
    writeln!(&mut output, "    @JvmStatic").unwrap();
    writeln!(&mut output, "    external fun updateBevy(deltaTime: Float): Boolean\n").unwrap();
    
    writeln!(&mut output, "    @JvmStatic").unwrap();
    writeln!(&mut output, "    external fun renderBevy(surface: Surface): Boolean\n").unwrap();
    
    writeln!(&mut output, "    @JvmStatic").unwrap();
    writeln!(&mut output, "    external fun shutdownBevy(): Boolean\n").unwrap();
    
    // Input handling
    writeln!(&mut output, "    // Input Handling").unwrap();
    writeln!(&mut output, "    @JvmStatic").unwrap();
    writeln!(&mut output, "    external fun sendTouchEvent(x: Float, y: Float, action: Int, pointerId: Int): Boolean\n").unwrap();
    
    writeln!(&mut output, "    @JvmStatic").unwrap();
    writeln!(&mut output, "    external fun sendSensorData(type: Int, values: FloatArray): Boolean\n").unwrap();
    
    // Lifecycle
    writeln!(&mut output, "    // Lifecycle Management").unwrap();
    writeln!(&mut output, "    @JvmStatic").unwrap();
    writeln!(&mut output, "    external fun onLifecycleEvent(event: Int): Boolean\n").unwrap();
    
    // Asset loading
    writeln!(&mut output, "    // Asset Management").unwrap();
    writeln!(&mut output, "    @JvmStatic").unwrap();
    writeln!(&mut output, "    external fun loadAsset(path: String): ByteArray?\n").unwrap();
    
    // Performance monitoring
    writeln!(&mut output, "    // Performance Monitoring").unwrap();
    writeln!(&mut output, "    @JvmStatic").unwrap();
    writeln!(&mut output, "    external fun getCurrentFps(): Float\n").unwrap();
    
    writeln!(&mut output, "    @JvmStatic").unwrap();
    writeln!(&mut output, "    external fun getMemoryUsage(): Long").unwrap();
    writeln!(&mut output, "}}\n").unwrap();
    
    // Engine wrapper class
    writeln!(&mut output, "/**").unwrap();
    writeln!(&mut output, " * High-level wrapper for Runetika engine").unwrap();
    writeln!(&mut output, " * Provides convenient Kotlin API with type safety").unwrap();
    writeln!(&mut output, " */").unwrap();
    writeln!(&mut output, "@Keep").unwrap();
    writeln!(&mut output, "class RunetikaEngine(private val context: Context) {{").unwrap();
    writeln!(&mut output, "    private var engineHandle: Long = 0").unwrap();
    writeln!(&mut output, "    private var isInitialized = false").unwrap();
    writeln!(&mut output, "    private var lastFrameTime = System.nanoTime()\n").unwrap();
    
    writeln!(&mut output, "    /**").unwrap();
    writeln!(&mut output, "     * Initialize the game engine").unwrap();
    writeln!(&mut output, "     */").unwrap();
    writeln!(&mut output, "    fun initialize(): Boolean {{").unwrap();
    writeln!(&mut output, "        if (isInitialized) return true\n").unwrap();
    writeln!(&mut output, "        val assetPath = context.filesDir.absolutePath").unwrap();
    writeln!(&mut output, "        val cachePath = context.cacheDir.absolutePath\n").unwrap();
    writeln!(&mut output, "        engineHandle = RuneikaNative.initBevy(assetPath, cachePath)").unwrap();
    writeln!(&mut output, "        isInitialized = engineHandle != 0L").unwrap();
    writeln!(&mut output, "        return isInitialized").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    /**").unwrap();
    writeln!(&mut output, "     * Update game logic").unwrap();
    writeln!(&mut output, "     */").unwrap();
    writeln!(&mut output, "    fun update(): Boolean {{").unwrap();
    writeln!(&mut output, "        if (!isInitialized) return false\n").unwrap();
    writeln!(&mut output, "        val currentTime = System.nanoTime()").unwrap();
    writeln!(&mut output, "        val deltaTime = (currentTime - lastFrameTime) / 1_000_000_000f").unwrap();
    writeln!(&mut output, "        lastFrameTime = currentTime\n").unwrap();
    writeln!(&mut output, "        return RuneikaNative.updateBevy(deltaTime)").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    /**").unwrap();
    writeln!(&mut output, "     * Render frame to surface").unwrap();
    writeln!(&mut output, "     */").unwrap();
    writeln!(&mut output, "    fun render(surface: Surface): Boolean {{").unwrap();
    writeln!(&mut output, "        if (!isInitialized) return false").unwrap();
    writeln!(&mut output, "        return RuneikaNative.renderBevy(surface)").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    /**").unwrap();
    writeln!(&mut output, "     * Handle touch events").unwrap();
    writeln!(&mut output, "     */").unwrap();
    writeln!(&mut output, "    fun handleTouch(event: MotionEvent): Boolean {{").unwrap();
    writeln!(&mut output, "        if (!isInitialized) return false\n").unwrap();
    writeln!(&mut output, "        val action = event.actionMasked").unwrap();
    writeln!(&mut output, "        val pointerIndex = event.actionIndex").unwrap();
    writeln!(&mut output, "        val pointerId = event.getPointerId(pointerIndex)").unwrap();
    writeln!(&mut output, "        val x = event.getX(pointerIndex)").unwrap();
    writeln!(&mut output, "        val y = event.getY(pointerIndex)\n").unwrap();
    writeln!(&mut output, "        return RuneikaNative.sendTouchEvent(x, y, action, pointerId)").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    /**").unwrap();
    writeln!(&mut output, "     * Handle sensor data").unwrap();
    writeln!(&mut output, "     */").unwrap();
    writeln!(&mut output, "    fun handleSensor(sensor: Sensor, values: FloatArray): Boolean {{").unwrap();
    writeln!(&mut output, "        if (!isInitialized) return false").unwrap();
    writeln!(&mut output, "        return RuneikaNative.sendSensorData(sensor.type, values)").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    /**").unwrap();
    writeln!(&mut output, "     * Handle lifecycle events").unwrap();
    writeln!(&mut output, "     */").unwrap();
    writeln!(&mut output, "    fun onLifecycleEvent(event: LifecycleEvent): Boolean {{").unwrap();
    writeln!(&mut output, "        if (!isInitialized && event != LifecycleEvent.CREATED) return false").unwrap();
    writeln!(&mut output, "        return RuneikaNative.onLifecycleEvent(event.ordinal)").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    /**").unwrap();
    writeln!(&mut output, "     * Shutdown the engine").unwrap();
    writeln!(&mut output, "     */").unwrap();
    writeln!(&mut output, "    fun shutdown() {{").unwrap();
    writeln!(&mut output, "        if (isInitialized) {{").unwrap();
    writeln!(&mut output, "            RuneikaNative.shutdownBevy()").unwrap();
    writeln!(&mut output, "            isInitialized = false").unwrap();
    writeln!(&mut output, "            engineHandle = 0").unwrap();
    writeln!(&mut output, "        }}").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    /**").unwrap();
    writeln!(&mut output, "     * Get current FPS").unwrap();
    writeln!(&mut output, "     */").unwrap();
    writeln!(&mut output, "    fun getFps(): Float = RuneikaNative.getCurrentFps()\n").unwrap();
    
    writeln!(&mut output, "    /**").unwrap();
    writeln!(&mut output, "     * Get memory usage in bytes").unwrap();
    writeln!(&mut output, "     */").unwrap();
    writeln!(&mut output, "    fun getMemoryUsage(): Long = RuneikaNative.getMemoryUsage()").unwrap();
    writeln!(&mut output, "}}\n").unwrap();
    
    // Lifecycle enum
    writeln!(&mut output, "/**").unwrap();
    writeln!(&mut output, " * Android lifecycle events").unwrap();
    writeln!(&mut output, " */").unwrap();
    writeln!(&mut output, "@Keep").unwrap();
    writeln!(&mut output, "enum class LifecycleEvent {{").unwrap();
    writeln!(&mut output, "    CREATED,").unwrap();
    writeln!(&mut output, "    STARTED,").unwrap();
    writeln!(&mut output, "    RESUMED,").unwrap();
    writeln!(&mut output, "    PAUSED,").unwrap();
    writeln!(&mut output, "    STOPPED,").unwrap();
    writeln!(&mut output, "    DESTROYED").unwrap();
    writeln!(&mut output, "}}").unwrap();
    
    output
}

/// Generate Kotlin activity example
pub fn generate_kotlin_activity() -> String {
    let mut output = String::new();
    
    writeln!(&mut output, "package com.runetika.android\n").unwrap();
    writeln!(&mut output, "import android.app.Activity").unwrap();
    writeln!(&mut output, "import android.os.Bundle").unwrap();
    writeln!(&mut output, "import android.view.SurfaceView").unwrap();
    writeln!(&mut output, "import android.view.SurfaceHolder").unwrap();
    writeln!(&mut output, "import android.view.MotionEvent\n").unwrap();
    
    writeln!(&mut output, "/**").unwrap();
    writeln!(&mut output, " * Example activity for Runetika game").unwrap();
    writeln!(&mut output, " */").unwrap();
    writeln!(&mut output, "class RunetikaActivity : Activity(), SurfaceHolder.Callback {{").unwrap();
    writeln!(&mut output, "    private lateinit var engine: RunetikaEngine").unwrap();
    writeln!(&mut output, "    private lateinit var surfaceView: SurfaceView").unwrap();
    writeln!(&mut output, "    private var renderThread: Thread? = null").unwrap();
    writeln!(&mut output, "    private var isRunning = false\n").unwrap();
    
    writeln!(&mut output, "    override fun onCreate(savedInstanceState: Bundle?) {{").unwrap();
    writeln!(&mut output, "        super.onCreate(savedInstanceState)").unwrap();
    writeln!(&mut output, "        ").unwrap();
    writeln!(&mut output, "        // Initialize engine").unwrap();
    writeln!(&mut output, "        engine = RunetikaEngine(this)").unwrap();
    writeln!(&mut output, "        engine.initialize()").unwrap();
    writeln!(&mut output, "        engine.onLifecycleEvent(LifecycleEvent.CREATED)").unwrap();
    writeln!(&mut output, "        ").unwrap();
    writeln!(&mut output, "        // Setup surface view").unwrap();
    writeln!(&mut output, "        surfaceView = SurfaceView(this)").unwrap();
    writeln!(&mut output, "        surfaceView.holder.addCallback(this)").unwrap();
    writeln!(&mut output, "        setContentView(surfaceView)").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    override fun surfaceCreated(holder: SurfaceHolder) {{").unwrap();
    writeln!(&mut output, "        startRenderThread(holder)").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    override fun surfaceChanged(holder: SurfaceHolder, format: Int, width: Int, height: Int) {{").unwrap();
    writeln!(&mut output, "        // Handle surface changes").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    override fun surfaceDestroyed(holder: SurfaceHolder) {{").unwrap();
    writeln!(&mut output, "        stopRenderThread()").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    private fun startRenderThread(holder: SurfaceHolder) {{").unwrap();
    writeln!(&mut output, "        isRunning = true").unwrap();
    writeln!(&mut output, "        renderThread = Thread {{").unwrap();
    writeln!(&mut output, "            while (isRunning) {{").unwrap();
    writeln!(&mut output, "                holder.surface?.let {{ surface ->").unwrap();
    writeln!(&mut output, "                    engine.update()").unwrap();
    writeln!(&mut output, "                    engine.render(surface)").unwrap();
    writeln!(&mut output, "                }}").unwrap();
    writeln!(&mut output, "            }}").unwrap();
    writeln!(&mut output, "        }}").unwrap();
    writeln!(&mut output, "        renderThread?.start()").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    private fun stopRenderThread() {{").unwrap();
    writeln!(&mut output, "        isRunning = false").unwrap();
    writeln!(&mut output, "        renderThread?.join()").unwrap();
    writeln!(&mut output, "        renderThread = null").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    override fun onTouchEvent(event: MotionEvent): Boolean {{").unwrap();
    writeln!(&mut output, "        return engine.handleTouch(event) || super.onTouchEvent(event)").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    override fun onResume() {{").unwrap();
    writeln!(&mut output, "        super.onResume()").unwrap();
    writeln!(&mut output, "        engine.onLifecycleEvent(LifecycleEvent.RESUMED)").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    override fun onPause() {{").unwrap();
    writeln!(&mut output, "        super.onPause()").unwrap();
    writeln!(&mut output, "        engine.onLifecycleEvent(LifecycleEvent.PAUSED)").unwrap();
    writeln!(&mut output, "    }}\n").unwrap();
    
    writeln!(&mut output, "    override fun onDestroy() {{").unwrap();
    writeln!(&mut output, "        super.onDestroy()").unwrap();
    writeln!(&mut output, "        engine.onLifecycleEvent(LifecycleEvent.DESTROYED)").unwrap();
    writeln!(&mut output, "        engine.shutdown()").unwrap();
    writeln!(&mut output, "    }}").unwrap();
    writeln!(&mut output, "}}").unwrap();
    
    output
}