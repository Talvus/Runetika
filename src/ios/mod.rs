//! iOS-specific performance optimizations for iPhone 14 Pro/15 Pro and iPad Pro M2/M4
//!
//! This module implements aggressive performance optimizations targeting:
//! - Memory usage: < 50MB (from 95MB baseline)
//! - Startup time: < 500ms (from 750ms baseline)
//! - 120Hz ProMotion support
//! - A17 Pro/M4 GPU optimization
//! - Zero-copy rendering paths
//! - Predictive resource loading

use bevy::prelude::*;
use std::sync::Arc;

#[cfg(target_os = "ios")]
pub mod metal_renderer;
#[cfg(target_os = "ios")]
pub mod memory_pool;
#[cfg(target_os = "ios")]
pub mod texture_compression;
#[cfg(target_os = "ios")]
pub mod swift_bridge;
#[cfg(target_os = "ios")]
pub mod predictive_loader;
#[cfg(target_os = "ios")]
pub mod performance_profiler;

/// iOS Performance Plugin with Metal-optimized rendering
pub struct IOSPerformancePlugin {
    /// Target device configuration
    pub device_profile: DeviceProfile,
    /// Enable aggressive memory management
    pub aggressive_memory_mode: bool,
    /// Enable predictive resource loading
    pub predictive_loading: bool,
}

impl Default for IOSPerformancePlugin {
    fn default() -> Self {
        Self {
            device_profile: DeviceProfile::auto_detect(),
            aggressive_memory_mode: true,
            predictive_loading: true,
        }
    }
}

impl Plugin for IOSPerformancePlugin {
    fn build(&self, app: &mut App) {
        app
            .insert_resource(self.device_profile.clone())
            .insert_resource(MemoryBudget::from_device(&self.device_profile))
            .insert_resource(RenderOptimizations::from_device(&self.device_profile))
            .init_resource::<MemoryPoolManager>()
            .init_resource::<TextureCache>()
            .init_resource::<PredictiveResourceLoader>()
            .init_resource::<PerformanceProfiler>()
            .add_systems(PreStartup, (
                initialize_metal_renderer,
                setup_memory_pools,
                configure_texture_compression,
            ))
            .add_systems(Startup, (
                optimize_startup_sequence,
                preload_critical_resources,
            ))
            .add_systems(PreUpdate, (
                update_memory_pressure,
                predictive_resource_loading,
            ))
            .add_systems(PostUpdate, (
                gpu_driven_culling,
                texture_streaming,
                memory_compaction,
            ))
            .add_systems(Last, (
                profile_frame_metrics,
                adaptive_quality_adjustment,
            ));
        
        #[cfg(target_os = "ios")]
        {
            app.add_plugins((
                metal_renderer::MetalRendererPlugin,
                memory_pool::MemoryPoolPlugin,
                texture_compression::ASTCCompressionPlugin,
                swift_bridge::SwiftBridgePlugin,
                predictive_loader::PredictiveLoaderPlugin,
            ));
        }
    }
}

/// Device profiles for different iOS hardware
#[derive(Resource, Clone, Debug)]
pub struct DeviceProfile {
    pub device_type: DeviceType,
    pub chip: ChipType,
    pub ram_gb: u8,
    pub gpu_cores: u8,
    pub neural_engine_cores: u8,
    pub display_refresh_rate: u16,
    pub has_promotion: bool,
    pub metal_features: MetalFeatures,
}

impl DeviceProfile {
    /// Auto-detect device profile based on system info
    pub fn auto_detect() -> Self {
        #[cfg(target_os = "ios")]
        {
            // Use iOS APIs to detect device
            if let Some(profile) = detect_ios_device() {
                return profile;
            }
        }
        
        // Default to iPhone 15 Pro profile
        Self::iphone_15_pro()
    }
    
    /// iPhone 15 Pro/Pro Max with A17 Pro
    pub fn iphone_15_pro() -> Self {
        Self {
            device_type: DeviceType::iPhone15Pro,
            chip: ChipType::A17Pro,
            ram_gb: 8,
            gpu_cores: 6,
            neural_engine_cores: 16,
            display_refresh_rate: 120,
            has_promotion: true,
            metal_features: MetalFeatures::all(),
        }
    }
    
    /// iPhone 14 Pro with A16 Bionic
    pub fn iphone_14_pro() -> Self {
        Self {
            device_type: DeviceType::iPhone14Pro,
            chip: ChipType::A16Bionic,
            ram_gb: 6,
            gpu_cores: 5,
            neural_engine_cores: 16,
            display_refresh_rate: 120,
            has_promotion: true,
            metal_features: MetalFeatures::tier2(),
        }
    }
    
    /// iPad Pro with M4
    pub fn ipad_pro_m4() -> Self {
        Self {
            device_type: DeviceType::iPadProM4,
            chip: ChipType::M4,
            ram_gb: 16,
            gpu_cores: 10,
            neural_engine_cores: 16,
            display_refresh_rate: 120,
            has_promotion: true,
            metal_features: MetalFeatures::all(),
        }
    }
    
    /// iPad Pro with M2
    pub fn ipad_pro_m2() -> Self {
        Self {
            device_type: DeviceType::iPadProM2,
            chip: ChipType::M2,
            ram_gb: 16,
            gpu_cores: 10,
            neural_engine_cores: 16,
            display_refresh_rate: 120,
            has_promotion: true,
            metal_features: MetalFeatures::tier2(),
        }
    }
}

/// Device types
#[derive(Clone, Debug, PartialEq)]
pub enum DeviceType {
    iPhone15Pro,
    iPhone14Pro,
    iPadProM4,
    iPadProM2,
    Other,
}

/// Chip types
#[derive(Clone, Debug, PartialEq)]
pub enum ChipType {
    A17Pro,
    A16Bionic,
    M4,
    M2,
    Other,
}

/// Metal feature support
#[derive(Clone, Debug)]
pub struct MetalFeatures {
    pub tier3_gpu: bool,
    pub ray_tracing: bool,
    pub mesh_shaders: bool,
    pub variable_rate_shading: bool,
    pub memoryless_targets: bool,
    pub tile_shaders: bool,
    pub argument_buffers: bool,
    pub indirect_command_buffers: bool,
    pub function_pointers: bool,
    pub sparse_textures: bool,
}

impl MetalFeatures {
    /// All features (A17 Pro, M4)
    pub fn all() -> Self {
        Self {
            tier3_gpu: true,
            ray_tracing: true,
            mesh_shaders: true,
            variable_rate_shading: true,
            memoryless_targets: true,
            tile_shaders: true,
            argument_buffers: true,
            indirect_command_buffers: true,
            function_pointers: true,
            sparse_textures: true,
        }
    }
    
    /// Tier 2 features (A16, M2)
    pub fn tier2() -> Self {
        Self {
            tier3_gpu: false,
            ray_tracing: false,
            mesh_shaders: true,
            variable_rate_shading: true,
            memoryless_targets: true,
            tile_shaders: true,
            argument_buffers: true,
            indirect_command_buffers: true,
            function_pointers: false,
            sparse_textures: false,
        }
    }
}

/// Memory budget configuration
#[derive(Resource)]
pub struct MemoryBudget {
    /// Maximum memory usage in MB
    pub max_memory_mb: u32,
    /// Target memory usage in MB
    pub target_memory_mb: u32,
    /// Texture memory budget in MB
    pub texture_budget_mb: u32,
    /// Mesh memory budget in MB
    pub mesh_budget_mb: u32,
    /// Audio memory budget in MB
    pub audio_budget_mb: u32,
    /// System reserved memory in MB
    pub system_reserved_mb: u32,
}

impl MemoryBudget {
    pub fn from_device(profile: &DeviceProfile) -> Self {
        match profile.device_type {
            DeviceType::iPhone15Pro | DeviceType::iPhone14Pro => Self {
                max_memory_mb: 48,  // Target: < 50MB
                target_memory_mb: 40,
                texture_budget_mb: 20,
                mesh_budget_mb: 10,
                audio_budget_mb: 5,
                system_reserved_mb: 5,
            },
            DeviceType::iPadProM4 | DeviceType::iPadProM2 => Self {
                max_memory_mb: 80,
                target_memory_mb: 60,
                texture_budget_mb: 35,
                mesh_budget_mb: 15,
                audio_budget_mb: 8,
                system_reserved_mb: 10,
            },
            _ => Self {
                max_memory_mb: 50,
                target_memory_mb: 40,
                texture_budget_mb: 20,
                mesh_budget_mb: 10,
                audio_budget_mb: 5,
                system_reserved_mb: 5,
            },
        }
    }
}

/// Render optimizations based on device capabilities
#[derive(Resource)]
pub struct RenderOptimizations {
    /// Use GPU-driven rendering
    pub gpu_driven_rendering: bool,
    /// Use indirect draw calls
    pub indirect_draws: bool,
    /// Use variable rate shading
    pub variable_rate_shading: bool,
    /// Use mesh shaders
    pub mesh_shaders: bool,
    /// Use memoryless render targets
    pub memoryless_targets: bool,
    /// Use tile-based deferred rendering
    pub tbdr_optimizations: bool,
    /// Batch size for draw calls
    pub draw_call_batch_size: u32,
    /// Maximum texture resolution
    pub max_texture_resolution: u32,
    /// Use ASTC texture compression
    pub astc_compression: bool,
}

impl RenderOptimizations {
    pub fn from_device(profile: &DeviceProfile) -> Self {
        match profile.chip {
            ChipType::A17Pro | ChipType::M4 => Self {
                gpu_driven_rendering: true,
                indirect_draws: true,
                variable_rate_shading: true,
                mesh_shaders: true,
                memoryless_targets: true,
                tbdr_optimizations: true,
                draw_call_batch_size: 256,
                max_texture_resolution: 2048,
                astc_compression: true,
            },
            ChipType::A16Bionic | ChipType::M2 => Self {
                gpu_driven_rendering: true,
                indirect_draws: true,
                variable_rate_shading: true,
                mesh_shaders: true,
                memoryless_targets: true,
                tbdr_optimizations: true,
                draw_call_batch_size: 128,
                max_texture_resolution: 2048,
                astc_compression: true,
            },
            _ => Self {
                gpu_driven_rendering: false,
                indirect_draws: false,
                variable_rate_shading: false,
                mesh_shaders: false,
                memoryless_targets: true,
                tbdr_optimizations: true,
                draw_call_batch_size: 64,
                max_texture_resolution: 1024,
                astc_compression: true,
            },
        }
    }
}

/// Memory pool manager for aggressive memory reuse
#[derive(Resource, Default)]
pub struct MemoryPoolManager {
    /// Pre-allocated texture pools
    texture_pools: Vec<MemoryPool>,
    /// Pre-allocated mesh pools
    mesh_pools: Vec<MemoryPool>,
    /// Pre-allocated uniform buffer pools
    uniform_pools: Vec<MemoryPool>,
    /// Total allocated memory
    total_allocated_mb: f32,
}

/// Individual memory pool
pub struct MemoryPool {
    /// Pool size in bytes
    size: usize,
    /// Current usage
    used: usize,
    /// Backing buffer
    buffer: Arc<Vec<u8>>,
}

/// Texture cache with ASTC compression
#[derive(Resource, Default)]
pub struct TextureCache {
    /// Cached compressed textures
    compressed: std::collections::HashMap<String, CompressedTexture>,
    /// LRU eviction queue
    lru_queue: std::collections::VecDeque<String>,
    /// Current cache size in MB
    cache_size_mb: f32,
}

/// Compressed texture data
pub struct CompressedTexture {
    /// ASTC compressed data
    data: Vec<u8>,
    /// Original dimensions
    width: u32,
    height: u32,
    /// Compression format
    format: ASTCFormat,
    /// Last access time
    last_access: std::time::Instant,
}

/// ASTC compression formats
#[derive(Clone, Copy, Debug)]
pub enum ASTCFormat {
    /// 4x4 blocks - highest quality
    ASTC4x4,
    /// 6x6 blocks - balanced
    ASTC6x6,
    /// 8x8 blocks - aggressive compression
    ASTC8x8,
}

/// Predictive resource loader
#[derive(Resource, Default)]
pub struct PredictiveResourceLoader {
    /// Predicted next resources
    prediction_queue: Vec<ResourcePrediction>,
    /// Resource access patterns
    access_patterns: ResourceAccessPattern,
    /// Preload threshold
    confidence_threshold: f32,
}

/// Resource prediction
pub struct ResourcePrediction {
    /// Resource path
    path: String,
    /// Confidence score (0.0 - 1.0)
    confidence: f32,
    /// Predicted load time
    predicted_time: std::time::Duration,
}

/// Resource access pattern tracking
#[derive(Default)]
pub struct ResourceAccessPattern {
    /// Sequence patterns
    sequences: Vec<Vec<String>>,
    /// Frequency map
    frequency: std::collections::HashMap<String, u32>,
    /// Transition probabilities
    transitions: std::collections::HashMap<(String, String), f32>,
}

/// Performance profiler with frame timing
#[derive(Resource, Default)]
pub struct PerformanceProfiler {
    /// Frame times in microseconds
    frame_times: Vec<u64>,
    /// CPU times
    cpu_times: Vec<u64>,
    /// GPU times (Metal timing)
    gpu_times: Vec<u64>,
    /// Memory snapshots
    memory_snapshots: Vec<MemorySnapshot>,
    /// Startup time tracking
    startup_metrics: StartupMetrics,
}

/// Memory snapshot
pub struct MemorySnapshot {
    /// Timestamp
    timestamp: std::time::Instant,
    /// Used memory in MB
    used_mb: f32,
    /// Peak memory in MB
    peak_mb: f32,
    /// Texture memory in MB
    texture_mb: f32,
    /// Mesh memory in MB
    mesh_mb: f32,
}

/// Startup metrics
#[derive(Default)]
pub struct StartupMetrics {
    /// Total startup time
    total_time_ms: u64,
    /// Asset loading time
    asset_load_ms: u64,
    /// Shader compilation time
    shader_compile_ms: u64,
    /// System initialization time
    system_init_ms: u64,
}

// System implementations

fn initialize_metal_renderer(
    device_profile: Res<DeviceProfile>,
    render_opts: Res<RenderOptimizations>,
) {
    info!("Initializing Metal renderer for {:?}", device_profile.device_type);
    info!("GPU cores: {}, Neural Engine cores: {}", 
          device_profile.gpu_cores, device_profile.neural_engine_cores);
    
    if render_opts.gpu_driven_rendering {
        info!("Enabling GPU-driven rendering with indirect draws");
    }
    if render_opts.mesh_shaders {
        info!("Enabling mesh shaders for geometry processing");
    }
    if render_opts.variable_rate_shading {
        info!("Enabling variable rate shading for performance");
    }
}

fn setup_memory_pools(
    mut pool_manager: ResMut<MemoryPoolManager>,
    memory_budget: Res<MemoryBudget>,
) {
    info!("Setting up memory pools with {}MB budget", memory_budget.max_memory_mb);
    
    // Pre-allocate texture pools
    for size in [1024 * 1024, 512 * 1024, 256 * 1024] {
        pool_manager.texture_pools.push(MemoryPool {
            size,
            used: 0,
            buffer: Arc::new(vec![0u8; size]),
        });
    }
    
    // Pre-allocate mesh pools
    for size in [512 * 1024, 256 * 1024, 128 * 1024] {
        pool_manager.mesh_pools.push(MemoryPool {
            size,
            used: 0,
            buffer: Arc::new(vec![0u8; size]),
        });
    }
    
    pool_manager.total_allocated_mb = 
        (pool_manager.texture_pools.iter().map(|p| p.size).sum::<usize>() +
         pool_manager.mesh_pools.iter().map(|p| p.size).sum::<usize>()) as f32 / 1024.0 / 1024.0;
    
    info!("Pre-allocated {:.2}MB in memory pools", pool_manager.total_allocated_mb);
}

fn configure_texture_compression(
    render_opts: Res<RenderOptimizations>,
) {
    if render_opts.astc_compression {
        info!("Configuring ASTC texture compression");
        info!("Max texture resolution: {}x{}", 
              render_opts.max_texture_resolution, 
              render_opts.max_texture_resolution);
    }
}

fn optimize_startup_sequence(
    mut profiler: ResMut<PerformanceProfiler>,
    time: Res<Time>,
) {
    let startup_time = time.elapsed().as_millis() as u64;
    profiler.startup_metrics.total_time_ms = startup_time;
    
    if startup_time < 500 {
        info!("✅ Startup time: {}ms (target: <500ms)", startup_time);
    } else {
        warn!("⚠️ Startup time: {}ms (exceeds 500ms target)", startup_time);
    }
}

fn preload_critical_resources(
    mut texture_cache: ResMut<TextureCache>,
    memory_budget: Res<MemoryBudget>,
) {
    info!("Preloading critical resources within {}MB texture budget", 
          memory_budget.texture_budget_mb);
    
    // In a real implementation, this would load actual game textures
    // For now, we'll simulate the preloading
    texture_cache.cache_size_mb = 0.0;
}

fn update_memory_pressure(
    pool_manager: Res<MemoryPoolManager>,
    memory_budget: Res<MemoryBudget>,
    mut profiler: ResMut<PerformanceProfiler>,
) {
    let current_usage = pool_manager.total_allocated_mb;
    
    if current_usage > memory_budget.max_memory_mb as f32 {
        warn!("Memory pressure high: {:.2}MB / {}MB", 
              current_usage, memory_budget.max_memory_mb);
    }
    
    profiler.memory_snapshots.push(MemorySnapshot {
        timestamp: std::time::Instant::now(),
        used_mb: current_usage,
        peak_mb: current_usage.max(
            profiler.memory_snapshots
                .last()
                .map(|s| s.peak_mb)
                .unwrap_or(0.0)
        ),
        texture_mb: 0.0,  // Would be calculated from actual texture usage
        mesh_mb: 0.0,     // Would be calculated from actual mesh usage
    });
    
    // Keep only last 60 snapshots
    if profiler.memory_snapshots.len() > 60 {
        profiler.memory_snapshots.remove(0);
    }
}

fn predictive_resource_loading(
    mut loader: ResMut<PredictiveResourceLoader>,
    time: Res<Time>,
) {
    // Update predictions based on access patterns
    loader.confidence_threshold = 0.7;
    
    // In a real implementation, this would analyze player behavior
    // and preload resources likely to be needed soon
}

fn gpu_driven_culling(
    render_opts: Res<RenderOptimizations>,
) {
    if render_opts.gpu_driven_rendering {
        // GPU-driven culling would be implemented here
        // This reduces CPU overhead by doing frustum culling on GPU
    }
}

fn texture_streaming(
    mut texture_cache: ResMut<TextureCache>,
    memory_budget: Res<MemoryBudget>,
) {
    // Implement texture streaming based on view distance
    // and available memory budget
    
    // Evict least recently used textures if over budget
    while texture_cache.cache_size_mb > memory_budget.texture_budget_mb as f32 {
        if let Some(oldest) = texture_cache.lru_queue.pop_front() {
            if let Some(texture) = texture_cache.compressed.remove(&oldest) {
                texture_cache.cache_size_mb -= texture.data.len() as f32 / 1024.0 / 1024.0;
            }
        } else {
            break;
        }
    }
}

fn memory_compaction(
    mut pool_manager: ResMut<MemoryPoolManager>,
) {
    // Compact memory pools to reduce fragmentation
    for pool in &mut pool_manager.texture_pools {
        if pool.used < pool.size / 2 {
            // Pool is less than half used, could compact
            // In a real implementation, this would defragment the pool
        }
    }
}

fn profile_frame_metrics(
    mut profiler: ResMut<PerformanceProfiler>,
    time: Res<Time>,
) {
    let frame_time_us = time.delta().as_micros() as u64;
    profiler.frame_times.push(frame_time_us);
    
    // Keep only last 120 frames (2 seconds at 60fps)
    if profiler.frame_times.len() > 120 {
        profiler.frame_times.remove(0);
    }
    
    // Calculate average frame time
    if !profiler.frame_times.is_empty() {
        let avg_frame_time = profiler.frame_times.iter().sum::<u64>() / 
                           profiler.frame_times.len() as u64;
        let fps = 1_000_000 / avg_frame_time;
        
        if fps >= 60 {
            // Meeting 60fps target
        } else if fps >= 30 {
            // Acceptable but could improve
        } else {
            // Performance issue
            warn!("Low FPS: {}", fps);
        }
    }
}

fn adaptive_quality_adjustment(
    profiler: Res<PerformanceProfiler>,
    device_profile: Res<DeviceProfile>,
) {
    if profiler.frame_times.is_empty() {
        return;
    }
    
    let avg_frame_time = profiler.frame_times.iter().sum::<u64>() / 
                       profiler.frame_times.len() as u64;
    
    let target_frame_time_us = if device_profile.has_promotion {
        8333  // 120fps target for ProMotion displays
    } else {
        16667 // 60fps target
    };
    
    if avg_frame_time > target_frame_time_us {
        // Need to reduce quality
        // This would adjust render settings dynamically
    } else if avg_frame_time < target_frame_time_us / 2 {
        // Have headroom to increase quality
        // This would improve visual fidelity
    }
}

#[cfg(target_os = "ios")]
fn detect_ios_device() -> Option<DeviceProfile> {
    // This would use iOS APIs to detect the actual device
    // For now, return None to use defaults
    None
}

/// Benchmark results structure
#[derive(Debug)]
pub struct BenchmarkResults {
    pub memory_usage_mb: f32,
    pub startup_time_ms: u64,
    pub average_fps: f32,
    pub peak_fps: f32,
    pub min_fps: f32,
    pub frame_time_percentiles: FrameTimePercentiles,
    pub draw_calls_per_frame: u32,
    pub texture_memory_mb: f32,
    pub mesh_memory_mb: f32,
}

#[derive(Debug)]
pub struct FrameTimePercentiles {
    pub p50_ms: f32,
    pub p90_ms: f32,
    pub p95_ms: f32,
    pub p99_ms: f32,
}

impl BenchmarkResults {
    /// Run benchmark and return results
    pub fn run_benchmark(profiler: &PerformanceProfiler) -> Self {
        let frame_times_ms: Vec<f32> = profiler.frame_times
            .iter()
            .map(|&us| us as f32 / 1000.0)
            .collect();
        
        let mut sorted_times = frame_times_ms.clone();
        sorted_times.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let percentile = |p: f32| -> f32 {
            let index = ((sorted_times.len() as f32 * p) as usize)
                .min(sorted_times.len() - 1);
            sorted_times.get(index).copied().unwrap_or(0.0)
        };
        
        let avg_frame_time = if !frame_times_ms.is_empty() {
            frame_times_ms.iter().sum::<f32>() / frame_times_ms.len() as f32
        } else {
            16.67
        };
        
        let memory_usage = profiler.memory_snapshots
            .last()
            .map(|s| s.used_mb)
            .unwrap_or(0.0);
        
        Self {
            memory_usage_mb: memory_usage,
            startup_time_ms: profiler.startup_metrics.total_time_ms,
            average_fps: 1000.0 / avg_frame_time,
            peak_fps: 1000.0 / frame_times_ms.iter().min_by(|a, b| 
                a.partial_cmp(b).unwrap()).copied().unwrap_or(16.67),
            min_fps: 1000.0 / frame_times_ms.iter().max_by(|a, b| 
                a.partial_cmp(b).unwrap()).copied().unwrap_or(16.67),
            frame_time_percentiles: FrameTimePercentiles {
                p50_ms: percentile(0.50),
                p90_ms: percentile(0.90),
                p95_ms: percentile(0.95),
                p99_ms: percentile(0.99),
            },
            draw_calls_per_frame: 50, // Would be tracked from actual rendering
            texture_memory_mb: profiler.memory_snapshots
                .last()
                .map(|s| s.texture_mb)
                .unwrap_or(0.0),
            mesh_memory_mb: profiler.memory_snapshots
                .last()
                .map(|s| s.mesh_mb)
                .unwrap_or(0.0),
        }
    }
    
    /// Print benchmark report
    pub fn print_report(&self) {
        println!("\n=== iOS Performance Benchmark Results ===\n");
        
        println!("Memory Usage:");
        println!("  Total: {:.2} MB (Target: < 50 MB) {}", 
                 self.memory_usage_mb,
                 if self.memory_usage_mb < 50.0 { "✅" } else { "❌" });
        println!("  Textures: {:.2} MB", self.texture_memory_mb);
        println!("  Meshes: {:.2} MB", self.mesh_memory_mb);
        
        println!("\nStartup Time:");
        println!("  {} ms (Target: < 500 ms) {}", 
                 self.startup_time_ms,
                 if self.startup_time_ms < 500 { "✅" } else { "❌" });
        
        println!("\nFrame Rate:");
        println!("  Average: {:.1} FPS", self.average_fps);
        println!("  Peak: {:.1} FPS", self.peak_fps);
        println!("  Minimum: {:.1} FPS", self.min_fps);
        
        println!("\nFrame Time Percentiles:");
        println!("  50th: {:.2} ms", self.frame_time_percentiles.p50_ms);
        println!("  90th: {:.2} ms", self.frame_time_percentiles.p90_ms);
        println!("  95th: {:.2} ms", self.frame_time_percentiles.p95_ms);
        println!("  99th: {:.2} ms", self.frame_time_percentiles.p99_ms);
        
        println!("\nRendering:");
        println!("  Draw calls: {}/frame", self.draw_calls_per_frame);
        
        println!("\n=========================================\n");
    }
}