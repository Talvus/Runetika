package com.runetika.android.performance

import android.app.ActivityManager
import android.content.ComponentCallbacks2
import android.content.Context
import android.content.res.Configuration
import android.graphics.Bitmap
import android.os.Build
import android.os.Debug
import android.util.Log
import android.util.LruCache
import androidx.annotation.RequiresApi
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.flow.*
import java.lang.ref.ReferenceQueue
import java.lang.ref.SoftReference
import java.lang.ref.WeakReference
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicLong
import kotlin.math.min

/**
 * Advanced memory management for Android's aggressive memory killer
 * Implements adaptive caching, memory pressure handling, and efficient GC coordination
 */
class MemoryManager(private val context: Context) : ComponentCallbacks2 {
    companion object {
        private const val TAG = "MemoryManager"
        
        // Memory thresholds
        private const val CRITICAL_MEMORY_THRESHOLD = 0.95f
        private const val HIGH_MEMORY_THRESHOLD = 0.85f
        private const val MEDIUM_MEMORY_THRESHOLD = 0.70f
        
        // Cache size ratios
        private const val TEXTURE_CACHE_RATIO = 0.30f
        private const val MESH_CACHE_RATIO = 0.20f
        private const val AUDIO_CACHE_RATIO = 0.10f
        private const val GENERAL_CACHE_RATIO = 0.15f
    }
    
    private val activityManager = context.getSystemService(Context.ACTIVITY_SERVICE) as ActivityManager
    private val memoryInfo = ActivityManager.MemoryInfo()
    
    // Memory tracking
    private val allocatedMemory = AtomicLong(0)
    private val peakMemory = AtomicLong(0)
    private val gcCount = AtomicLong(0)
    
    // Multi-tiered cache system
    private val textureCache: AdaptiveLruCache<String, TextureData>
    private val meshCache: AdaptiveLruCache<String, MeshData>
    private val audioCache: AdaptiveLruCache<String, AudioData>
    private val generalCache: AdaptiveLruCache<String, Any>
    
    // Weak reference cache for recently evicted items
    private val weakCache = ConcurrentHashMap<String, WeakReference<Any>>()
    private val weakReferenceQueue = ReferenceQueue<Any>()
    
    // Memory pressure monitoring
    private val memoryPressureFlow = MutableStateFlow(MemoryPressure.NORMAL)
    private var memoryMonitorJob: Job? = null
    
    // Native memory tracking
    private var nativeHeapSize = 0L
    private var nativeHeapAllocated = 0L
    
    init {
        // Initialize caches with adaptive sizes
        val maxMemory = getMaxAvailableMemory()
        
        textureCache = AdaptiveLruCache(
            (maxMemory * TEXTURE_CACHE_RATIO).toInt(),
            "TextureCache"
        )
        
        meshCache = AdaptiveLruCache(
            (maxMemory * MESH_CACHE_RATIO).toInt(),
            "MeshCache"
        )
        
        audioCache = AdaptiveLruCache(
            (maxMemory * AUDIO_CACHE_RATIO).toInt(),
            "AudioCache"
        )
        
        generalCache = AdaptiveLruCache(
            (maxMemory * GENERAL_CACHE_RATIO).toInt(),
            "GeneralCache"
        )
        
        // Register for memory callbacks
        context.registerComponentCallbacks(this)
    }
    
    /**
     * Start memory monitoring
     */
    fun startMonitoring() {
        memoryMonitorJob = GlobalScope.launch {
            while (isActive) {
                updateMemoryMetrics()
                checkMemoryPressure()
                cleanupWeakReferences()
                delay(1000) // Check every second
            }
        }
    }
    
    /**
     * Update memory metrics
     */
    private fun updateMemoryMetrics() {
        // Get system memory info
        activityManager.getMemoryInfo(memoryInfo)
        
        // Get app memory info
        val runtime = Runtime.getRuntime()
        val usedMemory = runtime.totalMemory() - runtime.freeMemory()
        val maxMemory = runtime.maxMemory()
        
        allocatedMemory.set(usedMemory)
        if (usedMemory > peakMemory.get()) {
            peakMemory.set(usedMemory)
        }
        
        // Get native heap info
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
            val nativeInfo = Debug.getNativeHeapSize()
            val nativeAllocated = Debug.getNativeHeapAllocatedSize()
            nativeHeapSize = nativeInfo
            nativeHeapAllocated = nativeAllocated
        }
        
        // Log detailed memory stats periodically
        if (gcCount.get() % 10 == 0L) {
            logMemoryStats()
        }
    }
    
    /**
     * Check and handle memory pressure
     */
    private fun checkMemoryPressure() {
        val runtime = Runtime.getRuntime()
        val usedMemory = runtime.totalMemory() - runtime.freeMemory()
        val maxMemory = runtime.maxMemory()
        val memoryUsage = usedMemory.toFloat() / maxMemory
        
        val newPressure = when {
            memoryUsage > CRITICAL_MEMORY_THRESHOLD || memoryInfo.lowMemory -> {
                MemoryPressure.CRITICAL
            }
            memoryUsage > HIGH_MEMORY_THRESHOLD -> {
                MemoryPressure.HIGH
            }
            memoryUsage > MEDIUM_MEMORY_THRESHOLD -> {
                MemoryPressure.MEDIUM
            }
            else -> MemoryPressure.NORMAL
        }
        
        if (memoryPressureFlow.value != newPressure) {
            memoryPressureFlow.value = newPressure
            handleMemoryPressureChange(newPressure)
        }
    }
    
    /**
     * Handle memory pressure changes
     */
    private fun handleMemoryPressureChange(pressure: MemoryPressure) {
        Log.w(TAG, "Memory pressure changed to: $pressure")
        
        when (pressure) {
            MemoryPressure.CRITICAL -> {
                // Emergency memory release
                emergencyMemoryRelease()
            }
            MemoryPressure.HIGH -> {
                // Aggressive cache trimming
                trimCaches(0.5f)
                // Suggest GC
                System.gc()
                gcCount.incrementAndGet()
            }
            MemoryPressure.MEDIUM -> {
                // Moderate cache trimming
                trimCaches(0.25f)
            }
            MemoryPressure.NORMAL -> {
                // Normal operation
            }
        }
    }
    
    /**
     * Emergency memory release for critical situations
     */
    private fun emergencyMemoryRelease() {
        Log.e(TAG, "EMERGENCY MEMORY RELEASE TRIGGERED")
        
        // Clear all caches immediately
        textureCache.evictAll()
        meshCache.evictAll()
        audioCache.evictAll()
        generalCache.evictAll()
        weakCache.clear()
        
        // Force garbage collection
        System.gc()
        System.runFinalization()
        System.gc()
        gcCount.addAndGet(3)
        
        // Notify native layer to release resources
        nativeEmergencyCleanup()
        
        // Reduce quality settings
        GlobalScope.launch {
            GameConfig.renderQuality = QualityLevel.LOW
            GameConfig.targetFPS = 30
        }
    }
    
    /**
     * Trim caches by percentage
     */
    private fun trimCaches(percentage: Float) {
        val trimAmount = min(1.0f, percentage)
        textureCache.trimToSize((textureCache.size() * (1 - trimAmount)).toInt())
        meshCache.trimToSize((meshCache.size() * (1 - trimAmount)).toInt())
        audioCache.trimToSize((audioCache.size() * (1 - trimAmount)).toInt())
        generalCache.trimToSize((generalCache.size() * (1 - trimAmount)).toInt())
    }
    
    /**
     * Clean up weak references
     */
    private fun cleanupWeakReferences() {
        var ref = weakReferenceQueue.poll()
        while (ref != null) {
            // Remove from weak cache
            weakCache.entries.removeIf { it.value == ref }
            ref = weakReferenceQueue.poll()
        }
    }
    
    /**
     * Cache texture with smart eviction
     */
    fun cacheTexture(key: String, texture: TextureData): Boolean {
        return when (memoryPressureFlow.value) {
            MemoryPressure.CRITICAL -> false // Don't cache in critical state
            MemoryPressure.HIGH -> {
                // Only cache if essential
                if (texture.priority > 0.8f) {
                    textureCache.put(key, texture)
                    true
                } else false
            }
            else -> {
                textureCache.put(key, texture)
                true
            }
        }
    }
    
    /**
     * Get texture from cache hierarchy
     */
    fun getTexture(key: String): TextureData? {
        // Try main cache first
        textureCache.get(key)?.let { return it }
        
        // Try weak cache
        weakCache[key]?.get()?.let { data ->
            if (data is TextureData) {
                // Promote back to main cache if memory allows
                if (memoryPressureFlow.value != MemoryPressure.CRITICAL) {
                    textureCache.put(key, data)
                }
                return data
            }
        }
        
        return null
    }
    
    /**
     * Preload critical assets
     */
    suspend fun preloadAssets(assets: List<AssetDescriptor>) = withContext(Dispatchers.IO) {
        val availableMemory = getAvailableMemory()
        var allocatedSize = 0L
        
        assets.sortedByDescending { it.priority }.forEach { asset ->
            if (allocatedSize + asset.estimatedSize < availableMemory * 0.5f) {
                when (asset.type) {
                    AssetType.TEXTURE -> loadTexture(asset)
                    AssetType.MESH -> loadMesh(asset)
                    AssetType.AUDIO -> loadAudio(asset)
                    AssetType.GENERAL -> loadGeneral(asset)
                }
                allocatedSize += asset.estimatedSize
            }
        }
    }
    
    /**
     * Get maximum available memory
     */
    private fun getMaxAvailableMemory(): Long {
        val runtime = Runtime.getRuntime()
        val maxMemory = runtime.maxMemory()
        
        // Consider device RAM
        activityManager.getMemoryInfo(memoryInfo)
        val totalMemory = memoryInfo.totalMem
        
        // Use conservative estimate
        return min(maxMemory, totalMemory / 4)
    }
    
    /**
     * Get currently available memory
     */
    private fun getAvailableMemory(): Long {
        val runtime = Runtime.getRuntime()
        val maxMemory = runtime.maxMemory()
        val usedMemory = runtime.totalMemory() - runtime.freeMemory()
        return maxMemory - usedMemory
    }
    
    /**
     * Log detailed memory statistics
     */
    private fun logMemoryStats() {
        val runtime = Runtime.getRuntime()
        val usedMemory = runtime.totalMemory() - runtime.freeMemory()
        val maxMemory = runtime.maxMemory()
        val percentage = (usedMemory.toFloat() / maxMemory * 100).toInt()
        
        Log.d(TAG, """
            Memory Stats:
            - Used: ${usedMemory / 1024 / 1024}MB / ${maxMemory / 1024 / 1024}MB ($percentage%)
            - Native Heap: ${nativeHeapAllocated / 1024 / 1024}MB / ${nativeHeapSize / 1024 / 1024}MB
            - Peak: ${peakMemory.get() / 1024 / 1024}MB
            - GC Count: ${gcCount.get()}
            - Cache Sizes: T:${textureCache.size()} M:${meshCache.size()} A:${audioCache.size()} G:${generalCache.size()}
            - Weak Cache: ${weakCache.size} items
            - Memory Pressure: ${memoryPressureFlow.value}
        """.trimIndent())
    }
    
    // ComponentCallbacks2 implementation
    override fun onConfigurationChanged(newConfig: Configuration) {
        // Handle configuration changes
    }
    
    override fun onLowMemory() {
        Log.w(TAG, "System low memory warning")
        handleMemoryPressureChange(MemoryPressure.CRITICAL)
    }
    
    override fun onTrimMemory(level: Int) {
        Log.d(TAG, "Trim memory request: $level")
        
        when (level) {
            ComponentCallbacks2.TRIM_MEMORY_COMPLETE -> {
                // App is not visible, release everything
                emergencyMemoryRelease()
            }
            ComponentCallbacks2.TRIM_MEMORY_MODERATE -> {
                // App is not visible, release moderate amount
                trimCaches(0.75f)
            }
            ComponentCallbacks2.TRIM_MEMORY_BACKGROUND -> {
                // App in background, release some resources
                trimCaches(0.5f)
            }
            ComponentCallbacks2.TRIM_MEMORY_UI_HIDDEN -> {
                // UI is hidden, release UI resources
                trimCaches(0.25f)
            }
            ComponentCallbacks2.TRIM_MEMORY_RUNNING_CRITICAL -> {
                // Running and critical memory
                handleMemoryPressureChange(MemoryPressure.CRITICAL)
            }
            ComponentCallbacks2.TRIM_MEMORY_RUNNING_LOW -> {
                // Running and low memory
                handleMemoryPressureChange(MemoryPressure.HIGH)
            }
            ComponentCallbacks2.TRIM_MEMORY_RUNNING_MODERATE -> {
                // Running and moderate memory
                handleMemoryPressureChange(MemoryPressure.MEDIUM)
            }
        }
    }
    
    /**
     * Cleanup resources
     */
    fun destroy() {
        memoryMonitorJob?.cancel()
        context.unregisterComponentCallbacks(this)
        textureCache.evictAll()
        meshCache.evictAll()
        audioCache.evictAll()
        generalCache.evictAll()
        weakCache.clear()
    }
    
    // Native methods
    private external fun nativeEmergencyCleanup()
    private external fun nativeGetMemoryStats(): MemoryStats
    
    // Asset loading methods
    private suspend fun loadTexture(descriptor: AssetDescriptor) {
        // Implementation
    }
    
    private suspend fun loadMesh(descriptor: AssetDescriptor) {
        // Implementation
    }
    
    private suspend fun loadAudio(descriptor: AssetDescriptor) {
        // Implementation
    }
    
    private suspend fun loadGeneral(descriptor: AssetDescriptor) {
        // Implementation
    }
}

/**
 * Adaptive LRU cache with automatic resizing
 */
class AdaptiveLruCache<K, V>(
    private var maxSize: Int,
    private val name: String
) : LruCache<K, V>(maxSize) {
    
    private val hitCount = AtomicLong(0)
    private val missCount = AtomicLong(0)
    
    override fun sizeOf(key: K, value: V): Int {
        return when (value) {
            is TextureData -> value.sizeInBytes
            is MeshData -> value.sizeInBytes
            is AudioData -> value.sizeInBytes
            is Bitmap -> value.byteCount
            else -> 1
        }
    }
    
    override fun entryRemoved(evicted: Boolean, key: K, oldValue: V, newValue: V?) {
        if (evicted) {
            // Add to weak cache if evicted
            if (oldValue != null) {
                MemoryManager.weakCache[key.toString()] = WeakReference(oldValue)
            }
        }
    }
    
    override fun get(key: K): V? {
        val value = super.get(key)
        if (value != null) {
            hitCount.incrementAndGet()
        } else {
            missCount.incrementAndGet()
        }
        return value
    }
    
    fun getHitRate(): Float {
        val total = hitCount.get() + missCount.get()
        return if (total > 0) hitCount.get().toFloat() / total else 0f
    }
    
    fun adaptSize(memoryPressure: MemoryPressure) {
        val newSize = when (memoryPressure) {
            MemoryPressure.CRITICAL -> maxSize / 4
            MemoryPressure.HIGH -> maxSize / 2
            MemoryPressure.MEDIUM -> (maxSize * 0.75).toInt()
            MemoryPressure.NORMAL -> maxSize
        }
        
        if (newSize != maxSize()) {
            resize(newSize)
            Log.d("AdaptiveLruCache", "$name resized to ${newSize / 1024 / 1024}MB")
        }
    }
}

// Support classes
enum class MemoryPressure {
    NORMAL, MEDIUM, HIGH, CRITICAL
}

data class TextureData(
    val width: Int,
    val height: Int,
    val format: Int,
    val data: ByteArray,
    val priority: Float = 0.5f
) {
    val sizeInBytes: Int get() = data.size
}

data class MeshData(
    val vertices: FloatArray,
    val indices: IntArray,
    val priority: Float = 0.5f
) {
    val sizeInBytes: Int get() = (vertices.size * 4) + (indices.size * 4)
}

data class AudioData(
    val samples: ByteArray,
    val sampleRate: Int,
    val channels: Int,
    val priority: Float = 0.5f
) {
    val sizeInBytes: Int get() = samples.size
}

data class AssetDescriptor(
    val path: String,
    val type: AssetType,
    val estimatedSize: Long,
    val priority: Float
)

enum class AssetType {
    TEXTURE, MESH, AUDIO, GENERAL
}

data class MemoryStats(
    val javaHeap: Long,
    val nativeHeap: Long,
    val graphics: Long,
    val stack: Long,
    val code: Long,
    val others: Long
)