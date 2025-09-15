package com.runetika.android.performance

import android.content.Context
import android.os.Build
import android.os.HardwarePropertiesManager
import android.os.PowerManager
import android.util.Log
import androidx.annotation.RequiresApi
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import java.io.File
import java.io.RandomAccessFile
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.math.max
import kotlin.math.min

/**
 * Thermal management system for preventing throttling on Snapdragon/Exynos
 * Monitors temperature and adjusts performance proactively
 */
class ThermalMonitor {
    companion object {
        private const val TAG = "ThermalMonitor"
        
        // Temperature thresholds (Celsius)
        private const val TEMP_NORMAL = 35f
        private const val TEMP_WARM = 40f
        private const val TEMP_HOT = 45f
        private const val TEMP_CRITICAL = 50f
        private const val TEMP_EMERGENCY = 55f
        
        // Thermal zones for different SoCs
        private val SNAPDRAGON_THERMAL_ZONES = listOf(
            "/sys/class/thermal/thermal_zone0/temp", // CPU
            "/sys/class/thermal/thermal_zone1/temp", // GPU
            "/sys/class/thermal/thermal_zone2/temp", // Battery
            "/sys/devices/virtual/thermal/tz-by-name/cpu-1-0-usr/temp",
            "/sys/devices/virtual/thermal/tz-by-name/gpu-usr/temp"
        )
        
        private val EXYNOS_THERMAL_ZONES = listOf(
            "/sys/class/thermal/thermal_zone0/temp",
            "/sys/class/thermal/thermal_zone4/temp", // Big cores
            "/sys/class/thermal/thermal_zone3/temp", // Little cores
            "/sys/devices/platform/10060000.tmu/temp"
        )
        
        private val TENSOR_THERMAL_ZONES = listOf(
            "/sys/class/thermal/thermal_zone0/temp",
            "/sys/class/thermal/thermal_zone16/temp", // TPU
            "/sys/class/thermal/thermal_zone17/temp", // GPU
            "/dev/thermal/tz-by-name/tpu_thermal"
        )
    }
    
    private val temperatureFlow = MutableStateFlow(25f)
    private val thermalStateFlow = MutableStateFlow(ThermalState.NORMAL)
    private var monitoringJob: Job? = null
    private val isMonitoring = AtomicBoolean(false)
    
    // SoC detection
    private val socType = detectSocType()
    private val thermalZones = selectThermalZones()
    
    /**
     * Start thermal monitoring
     */
    fun startMonitoring() {
        if (isMonitoring.getAndSet(true)) return
        
        monitoringJob = GlobalScope.launch {
            while (isActive) {
                val temp = readTemperature()
                temperatureFlow.value = temp
                
                val newState = calculateThermalState(temp)
                if (thermalStateFlow.value != newState) {
                    thermalStateFlow.value = newState
                    Log.d(TAG, "Thermal state changed: $newState (${temp}°C)")
                }
                
                delay(1000) // Check every second
            }
        }
    }
    
    /**
     * Stop monitoring
     */
    fun stopMonitoring() {
        isMonitoring.set(false)
        monitoringJob?.cancel()
    }
    
    /**
     * Get current temperature
     */
    fun getCurrentTemperature(): Float = temperatureFlow.value
    
    /**
     * Get thermal state
     */
    fun getThermalState(): ThermalState = thermalStateFlow.value
    
    /**
     * Detect SoC type
     */
    private fun detectSocType(): SocType {
        val hardware = Build.HARDWARE.lowercase()
        val board = Build.BOARD.lowercase()
        
        return when {
            hardware.contains("qcom") || board.contains("msm") || board.contains("sdm") -> {
                SocType.SNAPDRAGON
            }
            hardware.contains("exynos") || board.contains("universal") -> {
                SocType.EXYNOS
            }
            hardware.contains("tensor") || board.contains("gs") -> {
                SocType.TENSOR
            }
            hardware.contains("kirin") || board.contains("hi") -> {
                SocType.KIRIN
            }
            hardware.contains("mt") || board.contains("mediatek") -> {
                SocType.MEDIATEK
            }
            else -> SocType.UNKNOWN
        }
    }
    
    /**
     * Select thermal zones based on SoC
     */
    private fun selectThermalZones(): List<String> {
        return when (socType) {
            SocType.SNAPDRAGON -> SNAPDRAGON_THERMAL_ZONES
            SocType.EXYNOS -> EXYNOS_THERMAL_ZONES
            SocType.TENSOR -> TENSOR_THERMAL_ZONES
            else -> SNAPDRAGON_THERMAL_ZONES // Default to Snapdragon
        }
    }
    
    /**
     * Read temperature from thermal zones
     */
    private fun readTemperature(): Float {
        // Try hardware properties manager first (Android N+)
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.N) {
            val temp = readHardwareTemperature()
            if (temp > 0) return temp
        }
        
        // Fall back to reading thermal zones
        val temps = mutableListOf<Float>()
        
        for (zone in thermalZones) {
            try {
                val file = File(zone)
                if (file.exists() && file.canRead()) {
                    val temp = file.readText().trim().toFloatOrNull()
                    if (temp != null) {
                        // Most thermal zones report in millidegrees
                        val celsius = if (temp > 200) temp / 1000f else temp
                        temps.add(celsius)
                    }
                }
            } catch (e: Exception) {
                // Ignore individual zone failures
            }
        }
        
        // Return max temperature from all zones
        return temps.maxOrNull() ?: 25f
    }
    
    /**
     * Read temperature using HardwarePropertiesManager
     */
    @RequiresApi(Build.VERSION_CODES.N)
    private fun readHardwareTemperature(): Float {
        try {
            // This requires special permissions, usually only available to system apps
            // Keeping for completeness but will likely fail on regular apps
            return 0f
        } catch (e: Exception) {
            return 0f
        }
    }
    
    /**
     * Calculate thermal state from temperature
     */
    private fun calculateThermalState(temp: Float): ThermalState {
        return when {
            temp >= TEMP_EMERGENCY -> ThermalState.EMERGENCY
            temp >= TEMP_CRITICAL -> ThermalState.CRITICAL
            temp >= TEMP_HOT -> ThermalState.HOT
            temp >= TEMP_WARM -> ThermalState.WARM
            else -> ThermalState.NORMAL
        }
    }
}

/**
 * Adaptive quality controller that adjusts rendering based on performance
 */
class AdaptiveQualityController {
    companion object {
        private const val TAG = "AdaptiveQuality"
        
        // Frame time thresholds (nanoseconds)
        private const val TARGET_60FPS = 16_666_666L
        private const val TARGET_90FPS = 11_111_111L
        private const val TARGET_120FPS = 8_333_333L
        
        // Quality adjustment parameters
        private const val QUALITY_UP_THRESHOLD = 0.95f // 95% of target achieved
        private const val QUALITY_DOWN_THRESHOLD = 0.85f // Below 85% of target
        private const val QUALITY_CRITICAL_THRESHOLD = 0.70f // Below 70% needs immediate action
        
        // Stability requirements
        private const val STABLE_FRAMES_REQUIRED = 60 // 1 second at 60fps
        private const val COOLDOWN_FRAMES = 120 // 2 seconds between adjustments
    }
    
    private var currentQuality = QualityLevel.HIGH
    private var targetFrameTime = TARGET_60FPS
    private var stableFrameCount = 0
    private var lastAdjustmentFrame = 0
    private var currentFrame = 0
    
    // Performance tracking
    private val frameTimeHistory = CircularBuffer(120)
    private val qualityHistory = mutableListOf<QualityChange>()
    
    /**
     * Set target refresh rate
     */
    fun setTargetRefreshRate(rate: Int) {
        targetFrameTime = when (rate) {
            120 -> TARGET_120FPS
            90 -> TARGET_90FPS
            else -> TARGET_60FPS
        }
    }
    
    /**
     * Adjust quality based on frame statistics
     */
    fun adjustQuality(stats: FrameStats): QualityLevel {
        currentFrame++
        
        // Add to history
        frameTimeHistory.add(stats.averageFrameTime.toLong())
        
        // Check if we're in cooldown
        if (currentFrame - lastAdjustmentFrame < COOLDOWN_FRAMES) {
            return currentQuality
        }
        
        // Calculate performance ratio
        val performanceRatio = targetFrameTime.toFloat() / stats.averageFrameTime.toFloat()
        
        // Determine action based on performance
        val action = when {
            performanceRatio < QUALITY_CRITICAL_THRESHOLD -> QualityAction.DECREASE_IMMEDIATE
            performanceRatio < QUALITY_DOWN_THRESHOLD -> QualityAction.DECREASE
            performanceRatio > QUALITY_UP_THRESHOLD && stableFrameCount > STABLE_FRAMES_REQUIRED -> {
                QualityAction.INCREASE
            }
            else -> QualityAction.MAINTAIN
        }
        
        // Apply action
        when (action) {
            QualityAction.INCREASE -> {
                if (currentQuality.ordinal < QualityLevel.ULTRA.ordinal) {
                    currentQuality = QualityLevel.values()[currentQuality.ordinal + 1]
                    recordQualityChange(QualityChange.INCREASE, performanceRatio)
                    lastAdjustmentFrame = currentFrame
                    stableFrameCount = 0
                    Log.d(TAG, "Quality increased to: $currentQuality")
                }
            }
            QualityAction.DECREASE -> {
                if (currentQuality.ordinal > QualityLevel.POTATO.ordinal) {
                    currentQuality = QualityLevel.values()[currentQuality.ordinal - 1]
                    recordQualityChange(QualityChange.DECREASE, performanceRatio)
                    lastAdjustmentFrame = currentFrame
                    stableFrameCount = 0
                    Log.d(TAG, "Quality decreased to: $currentQuality")
                }
            }
            QualityAction.DECREASE_IMMEDIATE -> {
                // Drop two levels immediately
                val newLevel = max(0, currentQuality.ordinal - 2)
                currentQuality = QualityLevel.values()[newLevel]
                recordQualityChange(QualityChange.DECREASE_IMMEDIATE, performanceRatio)
                lastAdjustmentFrame = currentFrame
                stableFrameCount = 0
                Log.w(TAG, "Quality dropped immediately to: $currentQuality")
            }
            QualityAction.MAINTAIN -> {
                stableFrameCount++
            }
        }
        
        // Apply thermal throttling override
        currentQuality = applyThermalOverride(currentQuality, stats.thermalThrottle)
        
        return currentQuality
    }
    
    /**
     * Force quality reduction
     */
    fun forceQualityReduction() {
        if (currentQuality.ordinal > QualityLevel.LOW.ordinal) {
            currentQuality = QualityLevel.values()[currentQuality.ordinal - 1]
            lastAdjustmentFrame = currentFrame
            Log.w(TAG, "Forced quality reduction to: $currentQuality")
        }
    }
    
    /**
     * Apply thermal throttling override
     */
    private fun applyThermalOverride(quality: QualityLevel, thermalThrottle: Float): QualityLevel {
        return when {
            thermalThrottle <= 0.3f -> QualityLevel.POTATO
            thermalThrottle <= 0.5f -> QualityLevel.LOW
            thermalThrottle <= 0.7f -> QualityLevel.values()[min(quality.ordinal, QualityLevel.MEDIUM.ordinal)]
            else -> quality
        }
    }
    
    /**
     * Record quality change for analysis
     */
    private fun recordQualityChange(change: QualityChange, performanceRatio: Float) {
        qualityHistory.add(change)
        
        // Analyze patterns
        if (qualityHistory.size > 10) {
            val recentChanges = qualityHistory.takeLast(10)
            val oscillations = recentChanges.count { it == QualityChange.INCREASE } +
                              recentChanges.count { it == QualityChange.DECREASE }
            
            if (oscillations > 7) {
                Log.w(TAG, "Quality oscillation detected - stabilizing")
                // Prefer lower quality for stability
                if (currentQuality.ordinal > QualityLevel.MEDIUM.ordinal) {
                    currentQuality = QualityLevel.MEDIUM
                }
            }
        }
    }
    
    /**
     * Get quality statistics
     */
    fun getQualityStats(): QualityStats {
        return QualityStats(
            currentQuality = currentQuality,
            averageFrameTime = frameTimeHistory.average(),
            stabilityScore = stableFrameCount.toFloat() / STABLE_FRAMES_REQUIRED,
            qualityChanges = qualityHistory.size,
            targetFrameTime = targetFrameTime
        )
    }
}

/**
 * Touch prediction for low-latency input
 */
class TouchPredictor {
    private val historySize = 5
    private val xHistory = mutableListOf<Float>()
    private val yHistory = mutableListOf<Float>()
    private val timeHistory = mutableListOf<Long>()
    
    fun addSample(x: Float, y: Float, timestamp: Long) {
        xHistory.add(x)
        yHistory.add(y)
        timeHistory.add(timestamp)
        
        // Keep only recent history
        if (xHistory.size > historySize) {
            xHistory.removeAt(0)
            yHistory.removeAt(0)
            timeHistory.removeAt(0)
        }
    }
    
    fun predict(position: FloatArray, velocity: FloatArray, deltaTimeMs: Float): FloatArray {
        if (xHistory.size < 2) {
            return position
        }
        
        // Calculate acceleration
        val ax = if (xHistory.size >= 3) {
            val v1 = xHistory[xHistory.size - 1] - xHistory[xHistory.size - 2]
            val v2 = xHistory[xHistory.size - 2] - xHistory[xHistory.size - 3]
            v1 - v2
        } else 0f
        
        val ay = if (yHistory.size >= 3) {
            val v1 = yHistory[yHistory.size - 1] - yHistory[yHistory.size - 2]
            val v2 = yHistory[yHistory.size - 2] - yHistory[yHistory.size - 3]
            v1 - v2
        } else 0f
        
        // Predict using kinematic equation: s = ut + 0.5at²
        val t = deltaTimeMs / 1000f
        val predictedX = position[0] + velocity[0] * t + 0.5f * ax * t * t
        val predictedY = position[1] + velocity[1] * t + 0.5f * ay * t * t
        
        return floatArrayOf(predictedX, predictedY)
    }
}

// Support classes
enum class ThermalState {
    NORMAL, WARM, HOT, CRITICAL, EMERGENCY
}

enum class SocType {
    SNAPDRAGON, EXYNOS, TENSOR, KIRIN, MEDIATEK, UNKNOWN
}

enum class QualityAction {
    INCREASE, DECREASE, DECREASE_IMMEDIATE, MAINTAIN
}

enum class QualityChange {
    INCREASE, DECREASE, DECREASE_IMMEDIATE
}

data class QualityStats(
    val currentQuality: QualityLevel,
    val averageFrameTime: Double,
    val stabilityScore: Float,
    val qualityChanges: Int,
    val targetFrameTime: Long
)