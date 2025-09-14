/// FFI Type Definitions
/// 
/// This module defines all the C-compatible types used in the FFI bridge.
/// All types are designed to be safely passed across the FFI boundary.

use std::ffi::{c_char, c_void};
use std::time::SystemTime;

/// Result codes for FFI operations
pub const SUCCESS: i32 = 0;
pub const ERROR_NULL_HANDLE: i32 = -1;
pub const ERROR_INVALID_CONFIG: i32 = -2;
pub const ERROR_INIT_FAILED: i32 = -3;
pub const ERROR_ALREADY_INITIALIZED: i32 = -4;
pub const ERROR_LOCK_FAILED: i32 = -5;
pub const ERROR_INVALID_PARAMETER: i32 = -6;
pub const ERROR_ACTIVE_REFERENCES: i32 = -7;
pub const ERROR_RUNTIME: i32 = -8;
pub const ERROR_OUT_OF_MEMORY: i32 = -9;
pub const ERROR_INVALID_STATE: i32 = -10;

/// Callback function types
pub type ErrorCallback = Option<unsafe extern "C" fn(error_code: i32, message: *const c_char)>;
pub type LogCallback = Option<unsafe extern "C" fn(level: u32, message: *const c_char)>;
pub type FrameCallback = Option<unsafe extern "C" fn(framebuffer: u32, width: u32, height: u32)>;
pub type EventCallback = Option<unsafe extern "C" fn(event_type: u32, event_data: *const c_void)>;

/// Log levels matching iOS os_log levels
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogLevel {
    Debug = 0,
    Info = 1,
    Default = 2,
    Error = 3,
    Fault = 4,
}

/// Engine configuration passed from Swift
#[repr(C)]
#[derive(Debug, Clone)]
pub struct EngineConfig {
    /// Window width in points
    pub window_width: f32,
    /// Window height in points
    pub window_height: f32,
    /// Device scale factor (e.g., 2.0 for Retina, 3.0 for Super Retina)
    pub scale_factor: f32,
    /// Target frames per second
    pub target_fps: u32,
    /// Enable debug rendering
    pub debug_mode: bool,
    /// Enable performance monitoring
    pub enable_profiling: bool,
    /// Maximum number of touch points to track
    pub max_touches: u32,
    /// Audio enabled
    pub audio_enabled: bool,
    /// Use Metal backend (vs OpenGL ES)
    pub use_metal: bool,
    /// Reserved for future use
    pub reserved: [u64; 8],
}

impl Default for EngineConfig {
    fn default() -> Self {
        Self {
            window_width: 1170.0,  // iPhone 12 Pro width in points
            window_height: 2532.0,  // iPhone 12 Pro height in points
            scale_factor: 3.0,      // Super Retina scale
            target_fps: 60,
            debug_mode: false,
            enable_profiling: false,
            max_touches: 10,
            audio_enabled: true,
            use_metal: true,
            reserved: [0; 8],
        }
    }
}

impl EngineConfig {
    /// Parse configuration from raw pointer
    pub unsafe fn from_raw(raw: &EngineConfig) -> Result<Self, String> {
        // Validate configuration
        if raw.window_width <= 0.0 || raw.window_height <= 0.0 {
            return Err("Invalid window dimensions".to_string());
        }
        if raw.scale_factor <= 0.0 || raw.scale_factor > 4.0 {
            return Err("Invalid scale factor".to_string());
        }
        if raw.target_fps == 0 || raw.target_fps > 120 {
            return Err("Invalid target FPS".to_string());
        }
        if raw.max_touches == 0 || raw.max_touches > 20 {
            return Err("Invalid max touches".to_string());
        }
        
        Ok(raw.clone())
    }
}

/// Touch phases matching UITouch.Phase
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TouchPhase {
    Began = 0,
    Moved = 1,
    Stationary = 2,
    Ended = 3,
    Cancelled = 4,
}

impl TouchPhase {
    pub fn from_raw(raw: u32) -> Self {
        match raw {
            0 => TouchPhase::Began,
            1 => TouchPhase::Moved,
            2 => TouchPhase::Stationary,
            3 => TouchPhase::Ended,
            4 => TouchPhase::Cancelled,
            _ => TouchPhase::Cancelled,
        }
    }
}

/// Touch event data
#[repr(C)]
#[derive(Debug, Clone)]
pub struct TouchEvent {
    /// Unique identifier for this touch
    pub id: u64,
    /// Current phase of the touch
    pub phase: TouchPhase,
    /// Position in screen coordinates
    pub position: (f32, f32),
    /// Force of the touch (0.0 to 1.0, where 1.0 is maximum force)
    pub force: f32,
    /// Timestamp of the event
    pub timestamp: SystemTime,
}

/// Accelerometer event data
#[repr(C)]
#[derive(Debug, Clone)]
pub struct AccelerometerEvent {
    /// Acceleration in G-forces (x, y, z)
    pub acceleration: (f32, f32, f32),
    /// Timestamp of the reading
    pub timestamp: SystemTime,
}

/// Gyroscope event data
#[repr(C)]
#[derive(Debug, Clone)]
pub struct GyroscopeEvent {
    /// Rotation rate in radians/second (x, y, z)
    pub rotation_rate: (f32, f32, f32),
    /// Timestamp of the reading
    pub timestamp: SystemTime,
}

/// Device orientation
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeviceOrientation {
    Unknown = 0,
    Portrait = 1,
    PortraitUpsideDown = 2,
    LandscapeLeft = 3,
    LandscapeRight = 4,
    FaceUp = 5,
    FaceDown = 6,
}

/// App lifecycle events
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LifecycleEvent {
    WillEnterForeground = 0,
    DidBecomeActive = 1,
    WillResignActive = 2,
    DidEnterBackground = 3,
    WillTerminate = 4,
    MemoryWarning = 5,
}

/// Unified event type for iOS events
#[derive(Debug, Clone)]
pub enum IOSEvent {
    Touch(TouchEvent),
    Accelerometer(AccelerometerEvent),
    Gyroscope(GyroscopeEvent),
    Orientation(DeviceOrientation),
    Lifecycle(LifecycleEvent),
    Custom(u32, Vec<u8>),
}

impl IOSEvent {
    /// Get the raw event type for FFI
    pub fn as_raw_type(&self) -> u32 {
        match self {
            IOSEvent::Touch(_) => 1,
            IOSEvent::Accelerometer(_) => 2,
            IOSEvent::Gyroscope(_) => 3,
            IOSEvent::Orientation(_) => 4,
            IOSEvent::Lifecycle(_) => 5,
            IOSEvent::Custom(id, _) => 1000 + id,
        }
    }
    
    /// Get raw event data pointer for FFI
    pub fn as_raw_data(&self) -> *const c_void {
        match self {
            IOSEvent::Touch(event) => event as *const _ as *const c_void,
            IOSEvent::Accelerometer(event) => event as *const _ as *const c_void,
            IOSEvent::Gyroscope(event) => event as *const _ as *const c_void,
            IOSEvent::Orientation(orientation) => orientation as *const _ as *const c_void,
            IOSEvent::Lifecycle(event) => event as *const _ as *const c_void,
            IOSEvent::Custom(_, data) => data.as_ptr() as *const c_void,
        }
    }
}

/// Memory statistics for debugging
#[repr(C)]
#[derive(Debug, Clone, Default)]
pub struct MemoryStats {
    /// Total allocated bytes
    pub allocated_bytes: u64,
    /// Number of active allocations
    pub allocation_count: u64,
    /// Peak allocated bytes
    pub peak_bytes: u64,
    /// Number of deallocations
    pub deallocation_count: u64,
}

/// Performance metrics
#[repr(C)]
#[derive(Debug, Clone, Default)]
pub struct PerformanceMetrics {
    /// Current frames per second
    pub fps: f32,
    /// Frame time in milliseconds
    pub frame_time_ms: f32,
    /// Update time in milliseconds
    pub update_time_ms: f32,
    /// Render time in milliseconds
    pub render_time_ms: f32,
    /// Number of draw calls
    pub draw_calls: u32,
    /// Number of entities
    pub entity_count: u32,
    /// Memory statistics
    pub memory: MemoryStats,
}