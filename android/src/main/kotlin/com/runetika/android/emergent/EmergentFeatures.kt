package com.runetika.android.emergent

import android.content.Context
import android.hardware.Sensor
import android.hardware.SensorEvent
import android.hardware.SensorEventListener
import android.hardware.SensorManager
import android.hardware.display.DisplayManager
import android.os.Build
import android.os.VibrationEffect
import android.os.Vibrator
import android.os.VibratorManager
import android.view.Display
import android.view.MotionEvent
import android.view.Surface
import androidx.annotation.RequiresApi
import androidx.compose.animation.core.*
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.gestures.detectDragGestures
import androidx.compose.foundation.layout.*
import androidx.compose.material3.*
import androidx.compose.runtime.*
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.graphics.*
import androidx.compose.ui.graphics.drawscope.DrawScope
import androidx.compose.ui.graphics.drawscope.rotate
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.unit.dp
import androidx.window.layout.FoldingFeature
import androidx.window.layout.WindowInfoTracker
import androidx.window.layout.WindowLayoutInfo
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.math.*

/**
 * Foldable device gameplay mechanics
 * Creates unique puzzle mechanics using device folding
 */
@RequiresApi(Build.VERSION_CODES.R)
class FoldablePuzzleSystem(
    private val context: Context,
    private val scope: CoroutineScope
) {
    private val windowInfoTracker = WindowInfoTracker.getOrCreate(context)
    private val displayManager = context.getSystemService(Context.DISPLAY_SERVICE) as DisplayManager
    
    // Fold state
    private val _foldState = MutableStateFlow(FoldState.FLAT)
    val foldState: StateFlow<FoldState> = _foldState.asStateFlow()
    
    // Portal mechanics
    private val _activePortals = MutableStateFlow(emptyList<DimensionalPortal>())
    val activePortals: StateFlow<List<DimensionalPortal>> = _activePortals.asStateFlow()
    
    init {
        observeFoldingState()
    }
    
    /**
     * Observe device folding state changes
     */
    private fun observeFoldingState() {
        scope.launch {
            windowInfoTracker.windowLayoutInfo(context as android.app.Activity)
                .collect { layoutInfo ->
                    processFoldingFeatures(layoutInfo)
                }
        }
    }
    
    /**
     * Process folding features to create gameplay mechanics
     */
    private fun processFoldingFeatures(layoutInfo: WindowLayoutInfo) {
        val foldingFeature = layoutInfo.displayFeatures
            .filterIsInstance<FoldingFeature>()
            .firstOrNull()
        
        foldingFeature?.let { feature ->
            when (feature.state) {
                FoldingFeature.State.FLAT -> {
                    _foldState.value = FoldState.FLAT
                    closeAllPortals()
                }
                FoldingFeature.State.HALF_OPENED -> {
                    val angle = calculateFoldAngle(feature)
                    _foldState.value = FoldState.HALF_OPENED(angle)
                    
                    // Create portal at fold line
                    createFoldPortal(feature)
                    
                    // Trigger special mechanics based on angle
                    when {
                        angle < 90f -> activateMirrorMode(feature)
                        angle in 90f..135f -> enableDualPlayerMode(feature)
                        angle > 135f -> triggerSecretPath(feature)
                    }
                }
                else -> {
                    _foldState.value = FoldState.FLAT
                }
            }
        }
    }
    
    /**
     * Calculate fold angle from feature
     */
    private fun calculateFoldAngle(feature: FoldingFeature): Float {
        // Estimate angle based on feature bounds and orientation
        return when (feature.orientation) {
            FoldingFeature.Orientation.VERTICAL -> {
                // Vertical fold (book mode)
                val boundsRatio = feature.bounds.width().toFloat() / feature.bounds.height()
                180f * (1f - boundsRatio)
            }
            FoldingFeature.Orientation.HORIZONTAL -> {
                // Horizontal fold (laptop mode)
                val boundsRatio = feature.bounds.height().toFloat() / feature.bounds.width()
                180f * (1f - boundsRatio)
            }
            else -> 180f
        }
    }
    
    /**
     * Create a dimensional portal at the fold line
     */
    private fun createFoldPortal(feature: FoldingFeature) {
        val portal = DimensionalPortal(
            id = System.currentTimeMillis(),
            position = Offset(
                feature.bounds.centerX().toFloat(),
                feature.bounds.centerY().toFloat()
            ),
            orientation = when (feature.orientation) {
                FoldingFeature.Orientation.VERTICAL -> PortalOrientation.VERTICAL
                FoldingFeature.Orientation.HORIZONTAL -> PortalOrientation.HORIZONTAL
                else -> PortalOrientation.VERTICAL
            },
            type = PortalType.DIMENSIONAL_FOLD,
            energy = 1.0f
        )
        
        _activePortals.update { current ->
            current + portal
        }
        
        // Vibrate to indicate portal creation
        createPortalHaptics()
    }
    
    /**
     * Activate mirror mode for puzzle solving
     */
    private fun activateMirrorMode(feature: FoldingFeature) {
        // Mirror gameplay across fold
        scope.launch {
            // Send event to game engine
            GameEventBus.emit(
                MirrorModeEvent(
                    foldLine = feature.bounds,
                    active = true
                )
            )
        }
    }
    
    /**
     * Enable dual player mode on folded device
     */
    private fun enableDualPlayerMode(feature: FoldingFeature) {
        scope.launch {
            GameEventBus.emit(
                DualPlayerEvent(
                    screen1Bounds = calculateScreen1Bounds(feature),
                    screen2Bounds = calculateScreen2Bounds(feature),
                    active = true
                )
            )
        }
    }
    
    /**
     * Trigger secret path when device is nearly closed
     */
    private fun triggerSecretPath(feature: FoldingFeature) {
        scope.launch {
            GameEventBus.emit(
                SecretPathEvent(
                    unlocked = true,
                    foldAngle = calculateFoldAngle(feature)
                )
            )
        }
    }
    
    /**
     * Close all active portals
     */
    private fun closeAllPortals() {
        _activePortals.value = emptyList()
    }
    
    /**
     * Create haptic feedback for portal creation
     */
    @Suppress("DEPRECATION")
    private fun createPortalHaptics() {
        val vibrator = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            val vibratorManager = context.getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as VibratorManager
            vibratorManager.defaultVibrator
        } else {
            context.getSystemService(Context.VIBRATOR_SERVICE) as Vibrator
        }
        
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            // Create custom vibration pattern for portal
            val timings = longArrayOf(0, 50, 50, 100, 50, 200)
            val amplitudes = intArrayOf(0, 128, 0, 255, 0, 64)
            val effect = VibrationEffect.createWaveform(timings, amplitudes, -1)
            vibrator.vibrate(effect)
        } else {
            vibrator.vibrate(400)
        }
    }
    
    private fun calculateScreen1Bounds(feature: FoldingFeature): android.graphics.Rect {
        return when (feature.orientation) {
            FoldingFeature.Orientation.VERTICAL -> {
                android.graphics.Rect(0, 0, feature.bounds.left, feature.bounds.bottom)
            }
            FoldingFeature.Orientation.HORIZONTAL -> {
                android.graphics.Rect(0, 0, feature.bounds.right, feature.bounds.top)
            }
            else -> android.graphics.Rect()
        }
    }
    
    private fun calculateScreen2Bounds(feature: FoldingFeature): android.graphics.Rect {
        return when (feature.orientation) {
            FoldingFeature.Orientation.VERTICAL -> {
                android.graphics.Rect(feature.bounds.right, 0, feature.bounds.right * 2, feature.bounds.bottom)
            }
            FoldingFeature.Orientation.HORIZONTAL -> {
                android.graphics.Rect(0, feature.bounds.bottom, feature.bounds.right, feature.bounds.bottom * 2)
            }
            else -> android.graphics.Rect()
        }
    }
}

/**
 * Stylus/S-Pen integration for glyph drawing
 */
@RequiresApi(Build.VERSION_CODES.M)
class StylusGlyphSystem(
    private val context: Context,
    private val scope: CoroutineScope
) {
    // Glyph recognition
    private val glyphRecognizer = NeuralGlyphRecognizer()
    
    // Current glyph being drawn
    private val _currentGlyph = MutableStateFlow<Glyph3D?>(null)
    val currentGlyph: StateFlow<Glyph3D?> = _currentGlyph.asStateFlow()
    
    // Recognized glyphs
    private val _recognizedGlyphs = MutableStateFlow(emptyList<RecognizedGlyph>())
    val recognizedGlyphs: StateFlow<List<RecognizedGlyph>> = _recognizedGlyphs.asStateFlow()
    
    /**
     * Process stylus events for glyph creation
     */
    fun onStylusEvent(event: MotionEvent): Boolean {
        // Check if it's a stylus event
        if (event.getToolType(0) != MotionEvent.TOOL_TYPE_STYLUS) {
            return false
        }
        
        val pressure = event.pressure
        val tilt = event.getAxisValue(MotionEvent.AXIS_TILT)
        val orientation = event.orientation
        val distance = event.getAxisValue(MotionEvent.AXIS_DISTANCE)
        
        when (event.action) {
            MotionEvent.ACTION_DOWN -> {
                startGlyph(event.x, event.y, pressure, tilt, orientation)
            }
            MotionEvent.ACTION_MOVE -> {
                updateGlyph(event.x, event.y, pressure, tilt, orientation, distance)
            }
            MotionEvent.ACTION_UP -> {
                completeGlyph()
            }
            MotionEvent.ACTION_HOVER_MOVE -> {
                // Preview glyph power based on hover distance
                previewGlyphPower(distance)
            }
        }
        
        return true
    }
    
    /**
     * Start drawing a new glyph
     */
    private fun startGlyph(x: Float, y: Float, pressure: Float, tilt: Float, orientation: Float) {
        val glyph = Glyph3D(
            id = System.currentTimeMillis(),
            points = mutableListOf(
                GlyphPoint3D(x, y, pressure * MAX_GLYPH_DEPTH, System.currentTimeMillis())
            ),
            pressure = pressure,
            tilt = tilt,
            orientation = orientation,
            power = calculatePower(pressure, tilt, orientation),
            color = calculateGlyphColor(pressure)
        )
        
        _currentGlyph.value = glyph
        
        // Haptic feedback for glyph start
        provideDrawingHaptics(pressure)
    }
    
    /**
     * Update glyph as stylus moves
     */
    private fun updateGlyph(
        x: Float, 
        y: Float, 
        pressure: Float, 
        tilt: Float, 
        orientation: Float,
        distance: Float
    ) {
        _currentGlyph.update { current ->
            current?.apply {
                points.add(
                    GlyphPoint3D(
                        x = x,
                        y = y,
                        z = pressure * MAX_GLYPH_DEPTH,
                        timestamp = System.currentTimeMillis()
                    )
                )
                
                // Update glyph properties
                this.pressure = pressure
                this.tilt = tilt
                this.orientation = orientation
                this.power = calculatePower(pressure, tilt, orientation)
                
                // Adapt color based on pressure
                this.color = calculateGlyphColor(pressure)
            }
        }
        
        // Adaptive haptics based on pressure
        if (pressure > 0.7f) {
            provideDrawingHaptics(pressure)
        }
    }
    
    /**
     * Complete glyph and recognize it
     */
    private fun completeGlyph() {
        val glyph = _currentGlyph.value ?: return
        
        scope.launch {
            // Recognize glyph pattern
            val recognized = glyphRecognizer.recognize(glyph)
            
            if (recognized != null) {
                _recognizedGlyphs.update { current ->
                    current + recognized
                }
                
                // Trigger glyph effect
                triggerGlyphEffect(recognized)
                
                // Success haptics
                provideSuccessHaptics()
            } else {
                // Failure haptics
                provideFailureHaptics()
            }
            
            _currentGlyph.value = null
        }
    }
    
    /**
     * Preview glyph power based on hover distance
     */
    private fun previewGlyphPower(distance: Float) {
        // Show power preview UI
        val power = 1.0f - (distance / MAX_HOVER_DISTANCE).coerceIn(0f, 1f)
        
        scope.launch {
            GameEventBus.emit(
                GlyphPowerPreviewEvent(power = power)
            )
        }
    }
    
    /**
     * Calculate glyph power from stylus properties
     */
    private fun calculatePower(pressure: Float, tilt: Float, orientation: Float): Float {
        val pressureWeight = 0.5f
        val tiltWeight = 0.3f
        val orientationWeight = 0.2f
        
        val tiltFactor = 1.0f - (abs(tilt) / (PI / 2)).toFloat()
        val orientationFactor = abs(sin(orientation))
        
        return (pressure * pressureWeight + 
                tiltFactor * tiltWeight + 
                orientationFactor * orientationWeight).coerceIn(0f, 1f)
    }
    
    /**
     * Calculate glyph color based on pressure
     */
    private fun calculateGlyphColor(pressure: Float): Color {
        return Color.hsv(
            hue = 180f + (pressure * 180f), // Cyan to Magenta
            saturation = 0.8f,
            value = 0.5f + (pressure * 0.5f),
            alpha = 0.8f + (pressure * 0.2f)
        )
    }
    
    /**
     * Trigger effect when glyph is recognized
     */
    private fun triggerGlyphEffect(glyph: RecognizedGlyph) {
        scope.launch {
            when (glyph.type) {
                GlyphType.PORTAL -> createPortalAtGlyph(glyph)
                GlyphType.SHIELD -> activateShield(glyph)
                GlyphType.ATTACK -> launchAttack(glyph)
                GlyphType.HEAL -> applyHealing(glyph)
                GlyphType.TRANSFORM -> triggerTransformation(glyph)
            }
        }
    }
    
    // Effect implementations
    private suspend fun createPortalAtGlyph(glyph: RecognizedGlyph) {
        GameEventBus.emit(
            CreatePortalEvent(
                position = glyph.center,
                power = glyph.power
            )
        )
    }
    
    private suspend fun activateShield(glyph: RecognizedGlyph) {
        GameEventBus.emit(
            ActivateShieldEvent(
                duration = (glyph.power * 10000).toLong(),
                strength = glyph.power
            )
        )
    }
    
    private suspend fun launchAttack(glyph: RecognizedGlyph) {
        GameEventBus.emit(
            LaunchAttackEvent(
                direction = glyph.orientation,
                power = glyph.power
            )
        )
    }
    
    private suspend fun applyHealing(glyph: RecognizedGlyph) {
        GameEventBus.emit(
            HealingEvent(
                amount = (glyph.power * 100).toInt()
            )
        )
    }
    
    private suspend fun triggerTransformation(glyph: RecognizedGlyph) {
        GameEventBus.emit(
            TransformationEvent(
                type = determineTransformationType(glyph)
            )
        )
    }
    
    private fun determineTransformationType(glyph: RecognizedGlyph): TransformationType {
        return when {
            glyph.power > 0.8f -> TransformationType.ULTIMATE
            glyph.power > 0.5f -> TransformationType.ADVANCED
            else -> TransformationType.BASIC
        }
    }
    
    // Haptic feedback methods
    @Suppress("DEPRECATION")
    private fun provideDrawingHaptics(pressure: Float) {
        val vibrator = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            val vibratorManager = context.getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as VibratorManager
            vibratorManager.defaultVibrator
        } else {
            context.getSystemService(Context.VIBRATOR_SERVICE) as Vibrator
        }
        
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            val amplitude = (pressure * 255).toInt().coerceIn(1, 255)
            val effect = VibrationEffect.createOneShot(10, amplitude)
            vibrator.vibrate(effect)
        }
    }
    
    @Suppress("DEPRECATION")
    private fun provideSuccessHaptics() {
        val vibrator = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            val vibratorManager = context.getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as VibratorManager
            vibratorManager.defaultVibrator
        } else {
            context.getSystemService(Context.VIBRATOR_SERVICE) as Vibrator
        }
        
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
            vibrator.vibrate(VibrationEffect.createPredefined(VibrationEffect.EFFECT_CLICK))
        }
    }
    
    @Suppress("DEPRECATION")
    private fun provideFailureHaptics() {
        val vibrator = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            val vibratorManager = context.getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as VibratorManager
            vibratorManager.defaultVibrator
        } else {
            context.getSystemService(Context.VIBRATOR_SERVICE) as Vibrator
        }
        
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
            vibrator.vibrate(VibrationEffect.createPredefined(VibrationEffect.EFFECT_DOUBLE_CLICK))
        }
    }
    
    companion object {
        private const val MAX_GLYPH_DEPTH = 10f
        private const val MAX_HOVER_DISTANCE = 50f
    }
}

/**
 * Biometric gameplay integration
 */
@RequiresApi(Build.VERSION_CODES.O)
class BiometricGameplay(
    private val context: Context,
    private val scope: CoroutineScope
) : SensorEventListener {
    private val sensorManager = context.getSystemService(Context.SENSOR_SERVICE) as SensorManager
    
    // Heart rate monitoring
    private val _heartRate = MutableStateFlow(70)
    val heartRate: StateFlow<Int> = _heartRate.asStateFlow()
    
    // Stress level calculation
    private val _stressLevel = MutableStateFlow(StressLevel.CALM)
    val stressLevel: StateFlow<StressLevel> = _stressLevel.asStateFlow()
    
    // Gameplay modifiers based on biometrics
    private val _gameplayModifiers = MutableStateFlow(BiometricModifiers())
    val gameplayModifiers: StateFlow<BiometricModifiers> = _gameplayModifiers.asStateFlow()
    
    init {
        startBiometricMonitoring()
    }
    
    private fun startBiometricMonitoring() {
        // Register for heart rate sensor if available
        val heartRateSensor = sensorManager.getDefaultSensor(Sensor.TYPE_HEART_RATE)
        heartRateSensor?.let {
            sensorManager.registerListener(this, it, SensorManager.SENSOR_DELAY_NORMAL)
        }
        
        // Start stress calculation
        scope.launch {
            heartRate.collect { bpm ->
                updateStressLevel(bpm)
                updateGameplayModifiers(bpm)
            }
        }
    }
    
    override fun onSensorChanged(event: SensorEvent) {
        when (event.sensor.type) {
            Sensor.TYPE_HEART_RATE -> {
                _heartRate.value = event.values[0].toInt()
            }
        }
    }
    
    override fun onAccuracyChanged(sensor: Sensor?, accuracy: Int) {
        // Handle accuracy changes if needed
    }
    
    private fun updateStressLevel(bpm: Int) {
        val stress = when {
            bpm < 60 -> StressLevel.MEDITATION
            bpm < 80 -> StressLevel.CALM
            bpm < 100 -> StressLevel.NORMAL
            bpm < 120 -> StressLevel.ELEVATED
            else -> StressLevel.HIGH
        }
        
        _stressLevel.value = stress
        
        // Trigger special events based on stress
        scope.launch {
            when (stress) {
                StressLevel.MEDITATION -> {
                    // Unlock hidden glyphs during meditation
                    GameEventBus.emit(RevealHiddenGlyphsEvent())
                }
                StressLevel.HIGH -> {
                    // Increase difficulty when stressed
                    GameEventBus.emit(DifficultyModifierEvent(modifier = 1.5f))
                }
                else -> {
                    // Normal gameplay
                }
            }
        }
    }
    
    private fun updateGameplayModifiers(bpm: Int) {
        _gameplayModifiers.update { current ->
            current.copy(
                puzzleDifficulty = when {
                    bpm < 60 -> 0.7f  // Easier when calm
                    bpm > 100 -> 1.3f  // Harder when stressed
                    else -> 1.0f
                },
                energyRegenRate = when {
                    bpm in 80..100 -> 1.5f  // Optimal heart rate
                    else -> 1.0f
                },
                focusBonus = when {
                    bpm < 70 -> 2.0f  // Double focus when very calm
                    else -> 1.0f
                },
                hiddenPathsVisible = bpm < 60  // See hidden paths when meditating
            )
        }
    }
    
    fun cleanup() {
        sensorManager.unregisterListener(this)
    }
}

// Data classes and enums
sealed class FoldState {
    object FLAT : FoldState()
    data class HALF_OPENED(val angle: Float) : FoldState()
}

data class DimensionalPortal(
    val id: Long,
    val position: Offset,
    val orientation: PortalOrientation,
    val type: PortalType,
    val energy: Float
)

enum class PortalOrientation {
    VERTICAL, HORIZONTAL
}

enum class PortalType {
    DIMENSIONAL_FOLD,
    GLYPH_CREATED,
    TIME_RIFT
}

data class Glyph3D(
    val id: Long,
    val points: MutableList<GlyphPoint3D>,
    var pressure: Float,
    var tilt: Float,
    var orientation: Float,
    var power: Float,
    var color: Color
)

data class GlyphPoint3D(
    val x: Float,
    val y: Float,
    val z: Float,
    val timestamp: Long
)

data class RecognizedGlyph(
    val type: GlyphType,
    val confidence: Float,
    val power: Float,
    val center: Offset,
    val orientation: Float
)

enum class GlyphType {
    PORTAL, SHIELD, ATTACK, HEAL, TRANSFORM
}

enum class TransformationType {
    BASIC, ADVANCED, ULTIMATE
}

enum class StressLevel {
    MEDITATION, CALM, NORMAL, ELEVATED, HIGH
}

data class BiometricModifiers(
    val puzzleDifficulty: Float = 1.0f,
    val energyRegenRate: Float = 1.0f,
    val focusBonus: Float = 1.0f,
    val hiddenPathsVisible: Boolean = false
)

// Neural glyph recognizer (placeholder)
class NeuralGlyphRecognizer {
    suspend fun recognize(glyph: Glyph3D): RecognizedGlyph? {
        // Simulate recognition delay
        delay(100)
        
        // Simple pattern matching for demo
        return if (glyph.points.size > 10) {
            RecognizedGlyph(
                type = GlyphType.values().random(),
                confidence = 0.85f,
                power = glyph.power,
                center = Offset(
                    glyph.points.map { it.x }.average().toFloat(),
                    glyph.points.map { it.y }.average().toFloat()
                ),
                orientation = glyph.orientation
            )
        } else {
            null
        }
    }
}

// Event bus for game events
object GameEventBus {
    private val _events = MutableSharedFlow<GameEvent>()
    val events: SharedFlow<GameEvent> = _events.asSharedFlow()
    
    suspend fun emit(event: GameEvent) {
        _events.emit(event)
    }
}

// Game events
sealed class GameEvent

data class MirrorModeEvent(
    val foldLine: android.graphics.Rect,
    val active: Boolean
) : GameEvent()

data class DualPlayerEvent(
    val screen1Bounds: android.graphics.Rect,
    val screen2Bounds: android.graphics.Rect,
    val active: Boolean
) : GameEvent()

data class SecretPathEvent(
    val unlocked: Boolean,
    val foldAngle: Float
) : GameEvent()

data class GlyphPowerPreviewEvent(
    val power: Float
) : GameEvent()

data class CreatePortalEvent(
    val position: Offset,
    val power: Float
) : GameEvent()

data class ActivateShieldEvent(
    val duration: Long,
    val strength: Float
) : GameEvent()

data class LaunchAttackEvent(
    val direction: Float,
    val power: Float
) : GameEvent()

data class HealingEvent(
    val amount: Int
) : GameEvent()

data class TransformationEvent(
    val type: TransformationType
) : GameEvent()

data class RevealHiddenGlyphsEvent(
    val duration: Long = 10000L
) : GameEvent()

data class DifficultyModifierEvent(
    val modifier: Float
) : GameEvent()