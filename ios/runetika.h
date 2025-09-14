/**
 * Runetika iOS FFI Bridge
 * 
 * This header defines the C API for integrating Runetika with iOS/Swift.
 * 
 * Usage:
 * 1. Import this header in your bridging header
 * 2. Initialize the engine with runetika_init
 * 3. Call runetika_update and runetika_render in your game loop
 * 4. Send iOS events using the runetika_send_* functions
 * 5. Clean up with runetika_shutdown
 */

#ifndef RUNETIKA_H
#define RUNETIKA_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ===== Result Codes ===== */
#define RUNETIKA_SUCCESS                    0
#define RUNETIKA_ERROR_NULL_HANDLE          -1
#define RUNETIKA_ERROR_INVALID_CONFIG       -2
#define RUNETIKA_ERROR_INIT_FAILED          -3
#define RUNETIKA_ERROR_ALREADY_INITIALIZED  -4
#define RUNETIKA_ERROR_LOCK_FAILED          -5
#define RUNETIKA_ERROR_INVALID_PARAMETER    -6
#define RUNETIKA_ERROR_ACTIVE_REFERENCES    -7
#define RUNETIKA_ERROR_RUNTIME              -8
#define RUNETIKA_ERROR_OUT_OF_MEMORY        -9
#define RUNETIKA_ERROR_INVALID_STATE        -10

/* ===== Log Levels ===== */
typedef enum {
    RUNETIKA_LOG_DEBUG = 0,
    RUNETIKA_LOG_INFO = 1,
    RUNETIKA_LOG_DEFAULT = 2,
    RUNETIKA_LOG_ERROR = 3,
    RUNETIKA_LOG_FAULT = 4
} RunetikaLogLevel;

/* ===== Touch Phases ===== */
typedef enum {
    RUNETIKA_TOUCH_BEGAN = 0,
    RUNETIKA_TOUCH_MOVED = 1,
    RUNETIKA_TOUCH_STATIONARY = 2,
    RUNETIKA_TOUCH_ENDED = 3,
    RUNETIKA_TOUCH_CANCELLED = 4
} RunetikaTouchPhase;

/* ===== Device Orientation ===== */
typedef enum {
    RUNETIKA_ORIENTATION_UNKNOWN = 0,
    RUNETIKA_ORIENTATION_PORTRAIT = 1,
    RUNETIKA_ORIENTATION_PORTRAIT_UPSIDE_DOWN = 2,
    RUNETIKA_ORIENTATION_LANDSCAPE_LEFT = 3,
    RUNETIKA_ORIENTATION_LANDSCAPE_RIGHT = 4,
    RUNETIKA_ORIENTATION_FACE_UP = 5,
    RUNETIKA_ORIENTATION_FACE_DOWN = 6
} RunetikaDeviceOrientation;

/* ===== Lifecycle Events ===== */
typedef enum {
    RUNETIKA_LIFECYCLE_WILL_ENTER_FOREGROUND = 0,
    RUNETIKA_LIFECYCLE_DID_BECOME_ACTIVE = 1,
    RUNETIKA_LIFECYCLE_WILL_RESIGN_ACTIVE = 2,
    RUNETIKA_LIFECYCLE_DID_ENTER_BACKGROUND = 3,
    RUNETIKA_LIFECYCLE_WILL_TERMINATE = 4,
    RUNETIKA_LIFECYCLE_MEMORY_WARNING = 5
} RunetikaLifecycleEvent;

/* ===== Type Definitions ===== */

/** Opaque handle to the engine */
typedef struct RunetikaEngine RunetikaEngine;

/** Engine configuration */
typedef struct {
    float window_width;      /**< Window width in points */
    float window_height;     /**< Window height in points */
    float scale_factor;      /**< Device scale factor (e.g., 2.0 for Retina) */
    uint32_t target_fps;     /**< Target frames per second */
    bool debug_mode;         /**< Enable debug rendering */
    bool enable_profiling;   /**< Enable performance monitoring */
    uint32_t max_touches;    /**< Maximum number of touch points */
    bool audio_enabled;      /**< Enable audio */
    bool use_metal;          /**< Use Metal backend (vs OpenGL ES) */
    uint64_t reserved[8];    /**< Reserved for future use */
} RunetikaConfig;

/** Touch event data */
typedef struct {
    uint64_t id;            /**< Unique touch identifier */
    uint32_t phase;         /**< Touch phase (RunetikaTouchPhase) */
    float x;                /**< X position in screen coordinates */
    float y;                /**< Y position in screen coordinates */
    float force;            /**< Touch force (0.0 to 1.0) */
    uint64_t timestamp_sec; /**< Timestamp seconds */
    uint32_t timestamp_nsec;/**< Timestamp nanoseconds */
} RunetikaTouchEvent;

/** Memory statistics */
typedef struct {
    uint64_t allocated_bytes;     /**< Total allocated bytes */
    uint64_t allocation_count;     /**< Number of allocations */
    uint64_t peak_bytes;          /**< Peak allocated bytes */
    uint64_t deallocation_count;  /**< Number of deallocations */
} RunetikaMemoryStats;

/** Performance metrics */
typedef struct {
    float fps;                    /**< Current FPS */
    float frame_time_ms;          /**< Frame time in milliseconds */
    float update_time_ms;         /**< Update time in milliseconds */
    float render_time_ms;         /**< Render time in milliseconds */
    uint32_t draw_calls;          /**< Number of draw calls */
    uint32_t entity_count;        /**< Number of entities */
    RunetikaMemoryStats memory;   /**< Memory statistics */
} RunetikaPerformanceMetrics;

/** Buffer handle for data transfer */
typedef struct {
    uint8_t* data;      /**< Pointer to data */
    size_t size;        /**< Size of data */
    size_t capacity;    /**< Allocated capacity */
} RunetikaBuffer;

/* ===== Callback Types ===== */

/** Error callback function */
typedef void (*RunetikaErrorCallback)(int32_t error_code, const char* message);

/** Log callback function */
typedef void (*RunetikaLogCallback)(uint32_t level, const char* message);

/** Frame rendered callback */
typedef void (*RunetikaFrameCallback)(uint32_t framebuffer, uint32_t width, uint32_t height);

/** Event processed callback */
typedef void (*RunetikaEventCallback)(uint32_t event_type, const void* event_data);

/* ===== Core Functions ===== */

/**
 * Initialize the Runetika engine
 * 
 * @param config Engine configuration (can be NULL for defaults)
 * @param error_callback Callback for error reporting (can be NULL)
 * @return Engine handle on success, NULL on failure
 */
RunetikaEngine* runetika_init(const RunetikaConfig* config, RunetikaErrorCallback error_callback);

/**
 * Update the engine for one frame
 * 
 * @param engine Engine handle
 * @param delta_time Time since last update in seconds
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_update(RunetikaEngine* engine, float delta_time);

/**
 * Render the current frame
 * 
 * @param engine Engine handle
 * @param framebuffer Target framebuffer ID
 * @param width Viewport width
 * @param height Viewport height
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_render(RunetikaEngine* engine, uint32_t framebuffer, uint32_t width, uint32_t height);

/**
 * Shutdown the engine and release resources
 * 
 * @param engine Engine handle
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_shutdown(RunetikaEngine* engine);

/* ===== Event Functions ===== */

/**
 * Send a touch event to the engine
 * 
 * @param engine Engine handle
 * @param touch_id Unique touch identifier
 * @param phase Touch phase
 * @param x X position
 * @param y Y position
 * @param force Touch force (0.0 to 1.0)
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_send_touch(RunetikaEngine* engine, uint64_t touch_id, uint32_t phase, 
                            float x, float y, float force);

/**
 * Send multiple touch events at once
 * 
 * @param engine Engine handle
 * @param touches Array of touch events
 * @param count Number of touches
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_send_touches_batch(RunetikaEngine* engine, const RunetikaTouchEvent* touches, size_t count);

/**
 * Send accelerometer data
 * 
 * @param engine Engine handle
 * @param x X acceleration in G-forces
 * @param y Y acceleration in G-forces
 * @param z Z acceleration in G-forces
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_send_accelerometer(RunetikaEngine* engine, float x, float y, float z);

/**
 * Send gyroscope data
 * 
 * @param engine Engine handle
 * @param x X rotation rate in radians/second
 * @param y Y rotation rate in radians/second
 * @param z Z rotation rate in radians/second
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_send_gyroscope(RunetikaEngine* engine, float x, float y, float z);

/**
 * Send device orientation change
 * 
 * @param engine Engine handle
 * @param orientation Device orientation
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_send_orientation_event(RunetikaEngine* engine, uint32_t orientation);

/**
 * Send app lifecycle event
 * 
 * @param engine Engine handle
 * @param event Lifecycle event
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_send_lifecycle_event(RunetikaEngine* engine, uint32_t event);

/**
 * Send custom event with data
 * 
 * @param engine Engine handle
 * @param event_id Custom event ID
 * @param data Event data
 * @param data_size Size of data
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_send_custom_event(RunetikaEngine* engine, uint32_t event_id, 
                                   const uint8_t* data, size_t data_size);

/**
 * Clear all pending events
 * 
 * @param engine Engine handle
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_clear_events(RunetikaEngine* engine);

/**
 * Get number of pending events
 * 
 * @param engine Engine handle
 * @return Number of events or negative error code
 */
int32_t runetika_event_count(RunetikaEngine* engine);

/* ===== Callback Functions ===== */

/**
 * Set error callback
 * 
 * @param engine Engine handle
 * @param callback Error callback function
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_set_error_callback(RunetikaEngine* engine, RunetikaErrorCallback callback);

/**
 * Set log callback
 * 
 * @param engine Engine handle
 * @param callback Log callback function
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_set_log_callback(RunetikaEngine* engine, RunetikaLogCallback callback);

/* ===== Memory Management ===== */

/**
 * Allocate memory that can be passed between Rust and Swift
 * 
 * @param size Size in bytes
 * @return Pointer to allocated memory or NULL
 */
uint8_t* runetika_alloc(size_t size);

/**
 * Free memory allocated with runetika_alloc
 * 
 * @param ptr Pointer to memory
 * @param size Size in bytes
 */
void runetika_free(uint8_t* ptr, size_t size);

/**
 * Allocate zero-initialized memory
 * 
 * @param count Number of elements
 * @param size Size of each element
 * @return Pointer to allocated memory or NULL
 */
uint8_t* runetika_calloc(size_t count, size_t size);

/**
 * Reallocate memory
 * 
 * @param old_ptr Old pointer
 * @param old_size Old size
 * @param new_size New size
 * @return Pointer to reallocated memory or NULL
 */
uint8_t* runetika_realloc(uint8_t* old_ptr, size_t old_size, size_t new_size);

/**
 * Create a buffer for data transfer
 * 
 * @param data Data to copy
 * @param size Size of data
 * @return Buffer handle or NULL
 */
RunetikaBuffer* runetika_buffer_create(const uint8_t* data, size_t size);

/**
 * Free a buffer
 * 
 * @param buffer Buffer handle
 */
void runetika_buffer_free(RunetikaBuffer* buffer);

/* ===== Utility Functions ===== */

/**
 * Get version string
 * 
 * @return Version string (static, don't free)
 */
const char* runetika_version(void);

/**
 * Check if engine is initialized
 * 
 * @return true if initialized
 */
bool runetika_is_initialized(void);

/**
 * Retain a Swift reference
 * 
 * @return New reference count
 */
uint32_t runetika_retain(void);

/**
 * Release a Swift reference
 * 
 * @return New reference count
 */
uint32_t runetika_release(void);

/**
 * Get current Swift reference count
 * 
 * @return Reference count
 */
uint32_t runetika_ref_count(void);

/* ===== Performance Monitoring ===== */

/**
 * Get memory statistics
 * 
 * @param stats Output statistics
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_memory_stats(RunetikaMemoryStats* stats);

/**
 * Reset memory statistics
 */
void runetika_memory_stats_reset(void);

/**
 * Get performance metrics
 * 
 * @param engine Engine handle
 * @param metrics Output metrics
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_get_performance_metrics(RunetikaEngine* engine, RunetikaPerformanceMetrics* metrics);

/* ===== Logging ===== */

/**
 * Log a message
 * 
 * @param engine Engine handle
 * @param level Log level
 * @param message Message to log
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_log(RunetikaEngine* engine, uint32_t level, const char* message);

/**
 * Log a debug message
 * 
 * @param message Message to log
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_log_debug(const char* message);

/**
 * Log an info message
 * 
 * @param message Message to log
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_log_info(const char* message);

/**
 * Log an error message
 * 
 * @param message Message to log
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_log_error(const char* message);

/**
 * Flush log messages
 * 
 * @param engine Engine handle
 * @return RUNETIKA_SUCCESS or error code
 */
int32_t runetika_log_flush(RunetikaEngine* engine);

/* ===== Error Handling ===== */

/**
 * Get last error message
 * 
 * @return Error message or NULL (don't free)
 */
const char* runetika_get_last_error(void);

/**
 * Clear last error
 */
void runetika_clear_last_error(void);

/**
 * Check if there is a pending error
 * 
 * @return true if there is an error
 */
bool runetika_has_error(void);

/**
 * Convert error code to string
 * 
 * @param error_code Error code
 * @return Error string (static, don't free)
 */
const char* runetika_error_string(int32_t error_code);

#ifdef __cplusplus
}
#endif

#endif /* RUNETIKA_H */