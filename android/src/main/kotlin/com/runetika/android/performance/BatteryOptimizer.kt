package com.runetika.android.performance

import android.app.job.JobInfo
import android.app.job.JobParameters
import android.app.job.JobScheduler
import android.app.job.JobService
import android.content.BroadcastReceiver
import android.content.ComponentName
import android.content.Context
import android.content.Intent
import android.content.IntentFilter
import android.net.ConnectivityManager
import android.net.NetworkCapabilities
import android.os.*
import android.util.Log
import androidx.work.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger
import kotlin.math.max
import kotlin.math.min

/**
 * Advanced battery optimization system for Android
 * Manages Doze mode, battery saver, and adaptive power management
 */
class BatteryOptimizer(private val context: Context) {
    companion object {
        private const val TAG = "BatteryOptimizer"
        
        // Power states
        private const val POWER_STATE_HIGH_PERFORMANCE = 0
        private const val POWER_STATE_BALANCED = 1
        private const val POWER_STATE_BATTERY_SAVER = 2
        private const val POWER_STATE_ULTRA_BATTERY_SAVER = 3
        
        // Thresholds
        private const val CRITICAL_BATTERY_LEVEL = 15
        private const val LOW_BATTERY_LEVEL = 30
        private const val THERMAL_THROTTLE_TEMP = 40
        
        // Job IDs
        private const val JOB_ID_NETWORK_SYNC = 1001
        private const val JOB_ID_ANALYTICS = 1002
        private const val JOB_ID_RESOURCE_CLEANUP = 1003
    }
    
    private val powerManager = context.getSystemService(Context.POWER_SERVICE) as PowerManager
    private val batteryManager = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.LOLLIPOP) {
        context.getSystemService(Context.BATTERY_SERVICE) as BatteryManager
    } else null
    
    private val currentPowerState = AtomicInteger(POWER_STATE_BALANCED)
    private val isOptimizationActive = AtomicBoolean(false)
    
    // Doze mode detection
    private val isInDozeMode = AtomicBoolean(false)
    private val dozeModeReceiver = DozeModeReceiver()
    
    // Battery monitoring
    private val batteryLevelFlow = MutableStateFlow(100)
    private val isChargingFlow = MutableStateFlow(false)
    private val batteryTemperatureFlow = MutableStateFlow(25f) // Celsius
    
    // Network batching
    private val networkBatcher = NetworkRequestBatcher()
    
    // Wake lock management
    private var partialWakeLock: PowerManager.WakeLock? = null
    private val wakeLockRefCount = AtomicInteger(0)
    
    /**
     * Initialize battery optimization system
     */
    fun initialize() {
        if (isOptimizationActive.getAndSet(true)) return
        
        // Register battery and power receivers
        registerReceivers()
        
        // Setup WorkManager for background tasks
        setupWorkManager()
        
        // Initialize JobScheduler for API 21+
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.LOLLIPOP) {
            setupJobScheduler()
        }
        
        // Start monitoring
        startBatteryMonitoring()
        
        Log.d(TAG, "Battery optimization initialized")
    }
    
    /**
     * Register broadcast receivers for power events
     */
    private fun registerReceivers() {
        // Battery level and charging state
        val batteryFilter = IntentFilter().apply {
            addAction(Intent.ACTION_BATTERY_CHANGED)
            addAction(Intent.ACTION_POWER_CONNECTED)
            addAction(Intent.ACTION_POWER_DISCONNECTED)
            addAction(Intent.ACTION_BATTERY_LOW)
            addAction(Intent.ACTION_BATTERY_OKAY)
        }
        context.registerReceiver(BatteryReceiver(), batteryFilter)
        
        // Doze mode (Android 6.0+)
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
            val dozeFilter = IntentFilter().apply {
                addAction(PowerManager.ACTION_DEVICE_IDLE_MODE_CHANGED)
                addAction(PowerManager.ACTION_POWER_SAVE_MODE_CHANGED)
            }
            context.registerReceiver(dozeModeReceiver, dozeFilter)
        }
    }
    
    /**
     * Setup WorkManager for efficient background work
     */
    private fun setupWorkManager() {
        // Configure constraints for network sync
        val networkConstraints = Constraints.Builder()
            .setRequiredNetworkType(NetworkType.CONNECTED)
            .setRequiresBatteryNotLow(true)
            .setRequiresCharging(false) // Don't require charging for important syncs
            .build()
        
        // Periodic sync work (every 15 minutes minimum)
        val syncWork = PeriodicWorkRequestBuilder<NetworkSyncWorker>(
            15, TimeUnit.MINUTES,
            5, TimeUnit.MINUTES // Flex interval
        )
            .setConstraints(networkConstraints)
            .setBackoffCriteria(
                BackoffPolicy.EXPONENTIAL,
                WorkRequest.MIN_BACKOFF_MILLIS,
                TimeUnit.MILLISECONDS
            )
            .build()
        
        WorkManager.getInstance(context).enqueueUniquePeriodicWork(
            "network_sync",
            ExistingPeriodicWorkPolicy.KEEP,
            syncWork
        )
        
        // Analytics work (less critical, can wait for charging)
        val analyticsConstraints = Constraints.Builder()
            .setRequiredNetworkType(NetworkType.UNMETERED)
            .setRequiresBatteryNotLow(true)
            .setRequiresCharging(true)
            .setRequiresDeviceIdle(true) // Only when device is idle
            .build()
        
        val analyticsWork = PeriodicWorkRequestBuilder<AnalyticsWorker>(
            1, TimeUnit.DAYS
        )
            .setConstraints(analyticsConstraints)
            .build()
        
        WorkManager.getInstance(context).enqueueUniquePeriodicWork(
            "analytics",
            ExistingPeriodicWorkPolicy.KEEP,
            analyticsWork
        )
    }
    
    /**
     * Setup JobScheduler for older API compatibility
     */
    private fun setupJobScheduler() {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.LOLLIPOP) return
        
        val jobScheduler = context.getSystemService(Context.JOB_SCHEDULER_SERVICE) as JobScheduler
        
        // Network sync job
        val syncJobInfo = JobInfo.Builder(
            JOB_ID_NETWORK_SYNC,
            ComponentName(context, NetworkSyncJobService::class.java)
        ).apply {
            setRequiredNetworkType(JobInfo.NETWORK_TYPE_ANY)
            setPeriodic(TimeUnit.MINUTES.toMillis(30))
            setPersisted(true) // Survive reboots
            setRequiresBatteryNotLow(true)
        }.build()
        
        jobScheduler.schedule(syncJobInfo)
    }
    
    /**
     * Start battery monitoring coroutine
     */
    private fun startBatteryMonitoring() {
        GlobalScope.launch {
            // Monitor battery level
            batteryLevelFlow.collect { level ->
                adjustPowerState(level, isChargingFlow.value, batteryTemperatureFlow.value)
            }
        }
        
        GlobalScope.launch {
            // Monitor temperature
            batteryTemperatureFlow.collect { temp ->
                if (temp > THERMAL_THROTTLE_TEMP) {
                    applyThermalThrottling(temp)
                }
            }
        }
    }
    
    /**
     * Adjust power state based on battery conditions
     */
    private fun adjustPowerState(batteryLevel: Int, isCharging: Boolean, temperature: Float) {
        val newState = when {
            isCharging && batteryLevel > 80 -> POWER_STATE_HIGH_PERFORMANCE
            isCharging -> POWER_STATE_BALANCED
            batteryLevel <= CRITICAL_BATTERY_LEVEL -> POWER_STATE_ULTRA_BATTERY_SAVER
            batteryLevel <= LOW_BATTERY_LEVEL -> POWER_STATE_BATTERY_SAVER
            temperature > THERMAL_THROTTLE_TEMP -> POWER_STATE_BATTERY_SAVER
            else -> POWER_STATE_BALANCED
        }
        
        if (currentPowerState.getAndSet(newState) != newState) {
            applyPowerState(newState)
        }
    }
    
    /**
     * Apply power state optimizations
     */
    private fun applyPowerState(state: Int) {
        Log.d(TAG, "Applying power state: $state")
        
        when (state) {
            POWER_STATE_HIGH_PERFORMANCE -> {
                // Maximum performance
                setTargetFPS(120)
                setRenderQuality(QualityLevel.ULTRA)
                setNetworkBatching(false)
                setSensorPollingRate(SensorManager.SENSOR_DELAY_GAME)
            }
            
            POWER_STATE_BALANCED -> {
                // Balanced performance and battery
                setTargetFPS(60)
                setRenderQuality(QualityLevel.HIGH)
                setNetworkBatching(true, 5000) // 5 second batching
                setSensorPollingRate(SensorManager.SENSOR_DELAY_GAME)
            }
            
            POWER_STATE_BATTERY_SAVER -> {
                // Reduce performance for battery
                setTargetFPS(30)
                setRenderQuality(QualityLevel.MEDIUM)
                setNetworkBatching(true, 15000) // 15 second batching
                setSensorPollingRate(SensorManager.SENSOR_DELAY_NORMAL)
                reduceCPUFrequency()
            }
            
            POWER_STATE_ULTRA_BATTERY_SAVER -> {
                // Minimum power consumption
                setTargetFPS(24)
                setRenderQuality(QualityLevel.LOW)
                setNetworkBatching(true, 60000) // 1 minute batching
                setSensorPollingRate(SensorManager.SENSOR_DELAY_UI)
                reduceCPUFrequency()
                disableNonEssentialFeatures()
            }
        }
    }
    
    /**
     * Apply thermal throttling
     */
    private fun applyThermalThrottling(temperature: Float) {
        val throttleLevel = when {
            temperature > 50 -> 0.3f
            temperature > 45 -> 0.5f
            temperature > 40 -> 0.7f
            else -> 1.0f
        }
        
        Log.w(TAG, "Thermal throttling active: ${temperature}°C, level: $throttleLevel")
        
        // Reduce performance proportionally
        val targetFPS = (getCurrentTargetFPS() * throttleLevel).toInt()
        setTargetFPS(max(24, targetFPS))
    }
    
    /**
     * Efficiently acquire wake lock
     */
    fun acquireWakeLock(timeout: Long = 60000) {
        if (wakeLockRefCount.incrementAndGet() == 1) {
            partialWakeLock = powerManager.newWakeLock(
                PowerManager.PARTIAL_WAKE_LOCK,
                "Runetika::GameWakeLock"
            ).apply {
                acquire(timeout)
            }
        }
    }
    
    /**
     * Release wake lock
     */
    fun releaseWakeLock() {
        if (wakeLockRefCount.decrementAndGet() == 0) {
            partialWakeLock?.release()
            partialWakeLock = null
        }
    }
    
    /**
     * Check if we should defer work
     */
    fun shouldDeferWork(): Boolean {
        return when {
            isInDozeMode.get() -> true
            batteryLevelFlow.value <= CRITICAL_BATTERY_LEVEL && !isChargingFlow.value -> true
            batteryTemperatureFlow.value > THERMAL_THROTTLE_TEMP -> true
            else -> false
        }
    }
    
    /**
     * Batch network request for efficiency
     */
    fun batchNetworkRequest(request: NetworkRequest) {
        networkBatcher.addRequest(request)
    }
    
    /**
     * Force flush network requests
     */
    suspend fun flushNetworkRequests() {
        if (!shouldDeferWork()) {
            networkBatcher.flush()
        }
    }
    
    // Internal helper methods
    private fun setTargetFPS(fps: Int) {
        // Communicate with renderer
        GameConfig.targetFPS = fps
    }
    
    private fun setRenderQuality(quality: QualityLevel) {
        GameConfig.renderQuality = quality
    }
    
    private fun setNetworkBatching(enabled: Boolean, intervalMs: Int = 0) {
        networkBatcher.setBatching(enabled, intervalMs)
    }
    
    private fun setSensorPollingRate(rate: Int) {
        GameConfig.sensorPollingRate = rate
    }
    
    private fun reduceCPUFrequency() {
        // Hint to the system to reduce CPU frequency
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.N) {
            powerManager.addThermalStatusListener({ status ->
                Log.d(TAG, "Thermal status: $status")
            }, Handler(Looper.getMainLooper()))
        }
    }
    
    private fun disableNonEssentialFeatures() {
        // Disable particle effects, animations, etc.
        GameConfig.particleEffectsEnabled = false
        GameConfig.backgroundMusicEnabled = false
        GameConfig.hapticFeedbackEnabled = false
    }
    
    private fun getCurrentTargetFPS(): Int = GameConfig.targetFPS
    
    /**
     * Cleanup resources
     */
    fun destroy() {
        isOptimizationActive.set(false)
        releaseWakeLock()
        try {
            context.unregisterReceiver(dozeModeReceiver)
        } catch (e: Exception) {
            // Receiver might not be registered
        }
    }
    
    // Receiver classes
    inner class BatteryReceiver : BroadcastReceiver() {
        override fun onReceive(context: Context, intent: Intent) {
            when (intent.action) {
                Intent.ACTION_BATTERY_CHANGED -> {
                    val level = intent.getIntExtra(BatteryManager.EXTRA_LEVEL, -1)
                    val scale = intent.getIntExtra(BatteryManager.EXTRA_SCALE, -1)
                    val batteryPct = level * 100 / scale.toFloat()
                    batteryLevelFlow.value = batteryPct.toInt()
                    
                    val status = intent.getIntExtra(BatteryManager.EXTRA_STATUS, -1)
                    isChargingFlow.value = status == BatteryManager.BATTERY_STATUS_CHARGING ||
                                          status == BatteryManager.BATTERY_STATUS_FULL
                    
                    val temp = intent.getIntExtra(BatteryManager.EXTRA_TEMPERATURE, 0) / 10f
                    batteryTemperatureFlow.value = temp
                }
                Intent.ACTION_POWER_CONNECTED -> isChargingFlow.value = true
                Intent.ACTION_POWER_DISCONNECTED -> isChargingFlow.value = false
            }
        }
    }
    
    inner class DozeModeReceiver : BroadcastReceiver() {
        override fun onReceive(context: Context, intent: Intent) {
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
                when (intent.action) {
                    PowerManager.ACTION_DEVICE_IDLE_MODE_CHANGED -> {
                        isInDozeMode.set(powerManager.isDeviceIdleMode)
                        Log.d(TAG, "Doze mode: ${isInDozeMode.get()}")
                    }
                    PowerManager.ACTION_POWER_SAVE_MODE_CHANGED -> {
                        val isPowerSaveMode = powerManager.isPowerSaveMode
                        Log.d(TAG, "Power save mode: $isPowerSaveMode")
                        if (isPowerSaveMode) {
                            adjustPowerState(
                                batteryLevelFlow.value,
                                isChargingFlow.value,
                                batteryTemperatureFlow.value
                            )
                        }
                    }
                }
            }
        }
    }
}

/**
 * Network request batcher for efficiency
 */
class NetworkRequestBatcher {
    private val pendingRequests = mutableListOf<NetworkRequest>()
    private var batchingEnabled = false
    private var batchInterval = 5000L
    private var batchJob: Job? = null
    
    fun setBatching(enabled: Boolean, intervalMs: Int) {
        batchingEnabled = enabled
        batchInterval = intervalMs.toLong()
        
        if (enabled) {
            startBatchTimer()
        } else {
            batchJob?.cancel()
            flushImmediate()
        }
    }
    
    fun addRequest(request: NetworkRequest) {
        synchronized(pendingRequests) {
            pendingRequests.add(request)
        }
        
        if (!batchingEnabled) {
            flushImmediate()
        }
    }
    
    private fun startBatchTimer() {
        batchJob?.cancel()
        batchJob = GlobalScope.launch {
            delay(batchInterval)
            flush()
        }
    }
    
    suspend fun flush() {
        val requests = synchronized(pendingRequests) {
            val copy = pendingRequests.toList()
            pendingRequests.clear()
            copy
        }
        
        if (requests.isNotEmpty()) {
            executeBatch(requests)
        }
    }
    
    private fun flushImmediate() {
        GlobalScope.launch { flush() }
    }
    
    private suspend fun executeBatch(requests: List<NetworkRequest>) {
        // Execute all requests efficiently
        withContext(Dispatchers.IO) {
            requests.forEach { request ->
                try {
                    request.execute()
                } catch (e: Exception) {
                    Log.e("NetworkBatcher", "Request failed", e)
                }
            }
        }
    }
}

// Worker classes for WorkManager
class NetworkSyncWorker(
    context: Context,
    params: WorkerParameters
) : CoroutineWorker(context, params) {
    override suspend fun doWork(): Result {
        return try {
            // Perform network sync
            syncGameData()
            Result.success()
        } catch (e: Exception) {
            Result.retry()
        }
    }
    
    private suspend fun syncGameData() {
        // Implementation
    }
}

class AnalyticsWorker(
    context: Context,
    params: WorkerParameters
) : CoroutineWorker(context, params) {
    override suspend fun doWork(): Result {
        return try {
            // Send analytics
            sendAnalytics()
            Result.success()
        } catch (e: Exception) {
            Result.retry()
        }
    }
    
    private suspend fun sendAnalytics() {
        // Implementation
    }
}

// JobService for older APIs
class NetworkSyncJobService : JobService() {
    override fun onStartJob(params: JobParameters): Boolean {
        GlobalScope.launch {
            // Perform sync
            jobFinished(params, false)
        }
        return true
    }
    
    override fun onStopJob(params: JobParameters): Boolean {
        return true // Reschedule
    }
}

// Support classes
data class NetworkRequest(
    val url: String,
    val method: String,
    val body: ByteArray? = null,
    val headers: Map<String, String> = emptyMap(),
    val priority: Int = 0
) {
    suspend fun execute() {
        // Execute network request
    }
}

// Global game configuration
object GameConfig {
    var targetFPS = 60
    var renderQuality = QualityLevel.HIGH
    var sensorPollingRate = SensorManager.SENSOR_DELAY_GAME
    var particleEffectsEnabled = true
    var backgroundMusicEnabled = true
    var hapticFeedbackEnabled = true
}