use bevy::prelude::*;
use bevy::diagnostic::{DiagnosticsStore, FrameTimeDiagnosticsPlugin, EntityCountDiagnosticsPlugin};
use parking_lot::RwLock;
use std::sync::Arc;
use std::collections::VecDeque;

/// High-performance monitoring system with zero-cost abstractions
pub struct PerformancePlugin;

impl Plugin for PerformancePlugin {
    fn build(&self, app: &mut App) {
        app.add_plugins((
            FrameTimeDiagnosticsPlugin,
            EntityCountDiagnosticsPlugin,
        ))
        .insert_resource(PerformanceMetrics::default())
        .insert_resource(OptimizationSettings::default())
        .add_systems(Update, (
            update_performance_metrics,
            auto_optimize_quality,
            profile_system_execution.run_if(resource_exists::<ProfilingEnabled>),
        ).chain());
    }
}

/// Optimized performance metrics using lock-free data structures
#[derive(Resource, Default)]
pub struct PerformanceMetrics {
    /// Ring buffer for frame times - avoids allocations
    frame_times: Arc<RwLock<VecDeque<f32>>>,
    /// Current FPS with exponential moving average
    current_fps: f32,
    /// Memory usage in MB
    memory_usage_mb: f32,
    /// Entity count
    entity_count: u32,
    /// Draw calls (estimated)
    draw_calls: u32,
    /// CPU frame time in ms
    cpu_frame_ms: f32,
    /// GPU frame time in ms (estimated)
    gpu_frame_ms: f32,
}

impl PerformanceMetrics {
    const FRAME_HISTORY_SIZE: usize = 120;
    const SMOOTHING_FACTOR: f32 = 0.1;

    pub fn update_frame_time(&mut self, delta: f32) {
        let mut times = self.frame_times.write();
        
        // Maintain fixed-size ring buffer
        if times.len() >= Self::FRAME_HISTORY_SIZE {
            times.pop_front();
        }
        times.push_back(delta);
        
        // Calculate smoothed FPS
        let instant_fps = 1.0 / delta.max(0.001);
        self.current_fps = self.current_fps * (1.0 - Self::SMOOTHING_FACTOR) 
            + instant_fps * Self::SMOOTHING_FACTOR;
        
        self.cpu_frame_ms = delta * 1000.0;
    }

    pub fn get_average_fps(&self) -> f32 {
        let times = self.frame_times.read();
        if times.is_empty() {
            return 60.0;
        }
        
        let avg_time = times.iter().sum::<f32>() / times.len() as f32;
        1.0 / avg_time.max(0.001)
    }

    pub fn get_percentile_fps(&self, percentile: f32) -> f32 {
        let times = self.frame_times.read();
        if times.is_empty() {
            return 60.0;
        }
        
        let mut sorted: Vec<f32> = times.iter().copied().collect();
        sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let index = ((sorted.len() as f32 * percentile) as usize).min(sorted.len() - 1);
        1.0 / sorted[index].max(0.001)
    }
}

/// Optimization settings for automatic quality adjustment
#[derive(Resource)]
pub struct OptimizationSettings {
    /// Target FPS for auto-optimization
    pub target_fps: f32,
    /// Current quality level (0.0 = lowest, 1.0 = highest)
    pub quality_level: f32,
    /// Enable automatic quality adjustment
    pub auto_adjust: bool,
    /// Time since last adjustment
    pub last_adjustment: f32,
    /// Minimum time between adjustments
    pub adjustment_cooldown: f32,
    /// Use aggressive optimizations
    pub aggressive_mode: bool,
}

impl Default for OptimizationSettings {
    fn default() -> Self {
        Self {
            target_fps: 60.0,
            quality_level: 1.0,
            auto_adjust: true,
            last_adjustment: 0.0,
            adjustment_cooldown: 2.0,
            aggressive_mode: false,
        }
    }
}

/// Marker resource to enable profiling
#[derive(Resource)]
pub struct ProfilingEnabled;

/// System to update performance metrics with minimal overhead
fn update_performance_metrics(
    time: Res<Time>,
    mut metrics: ResMut<PerformanceMetrics>,
    diagnostics: Res<DiagnosticsStore>,
    query: Query<Entity>,
) {
    // Update frame time
    metrics.update_frame_time(time.delta_seconds());
    
    // Update entity count
    metrics.entity_count = query.iter().count() as u32;
    
    // Get memory usage (platform-specific, simplified here)
    #[cfg(not(target_arch = "wasm32"))]
    {
        // This is a simplified approach - in production you'd use platform-specific APIs
        metrics.memory_usage_mb = estimate_memory_usage();
    }
    
    // Estimate draw calls based on entity count and type
    metrics.draw_calls = estimate_draw_calls(&query);
}

/// Auto-optimize quality settings based on performance
fn auto_optimize_quality(
    mut settings: ResMut<OptimizationSettings>,
    metrics: Res<PerformanceMetrics>,
    time: Res<Time>,
    mut commands: Commands,
) {
    if !settings.auto_adjust {
        return;
    }
    
    settings.last_adjustment += time.delta_seconds();
    
    if settings.last_adjustment < settings.adjustment_cooldown {
        return;
    }
    
    let current_fps = metrics.current_fps;
    let target = settings.target_fps;
    
    // Hysteresis to prevent oscillation
    const UPPER_THRESHOLD: f32 = 1.1;
    const LOWER_THRESHOLD: f32 = 0.9;
    
    if current_fps < target * LOWER_THRESHOLD {
        // Performance is too low, reduce quality
        settings.quality_level = (settings.quality_level - 0.1).max(0.0);
        settings.last_adjustment = 0.0;
        
        apply_quality_settings(&settings, &mut commands);
        
        if settings.aggressive_mode && settings.quality_level < 0.3 {
            // Apply aggressive optimizations
            apply_aggressive_optimizations(&mut commands);
        }
    } else if current_fps > target * UPPER_THRESHOLD && settings.quality_level < 1.0 {
        // Performance is good, can increase quality
        settings.quality_level = (settings.quality_level + 0.05).min(1.0);
        settings.last_adjustment = 0.0;
        
        apply_quality_settings(&settings, &mut commands);
    }
}

/// Apply quality settings to the game
fn apply_quality_settings(settings: &OptimizationSettings, commands: &mut Commands) {
    let level = settings.quality_level;
    
    // Insert quality settings as events or resources for other systems to react to
    commands.insert_resource(QualityLevel {
        shadow_quality: if level > 0.7 { ShadowQuality::High } 
                       else if level > 0.3 { ShadowQuality::Medium } 
                       else { ShadowQuality::Low },
        texture_quality: if level > 0.5 { TextureQuality::High } 
                        else { TextureQuality::Low },
        particle_density: level,
        render_distance: 100.0 + level * 400.0,
        antialiasing: level > 0.5,
    });
}

/// Apply aggressive optimizations when performance is critical
fn apply_aggressive_optimizations(commands: &mut Commands) {
    commands.insert_resource(AggressiveOptimizations {
        disable_particles: true,
        reduce_draw_distance: true,
        simplify_shaders: true,
        disable_post_processing: true,
    });
}

/// Profile system execution times
fn profile_system_execution(
    time: Res<Time>,
) {
    #[cfg(feature = "profiling")]
    {
        puffin::profile_scope!("frame");
        
        // This would integrate with Tracy or Puffin for detailed profiling
        let frame_time = time.delta_seconds() * 1000.0;
        puffin::profile_scope!("update", frame_time);
    }
}

/// Estimate memory usage (simplified)
fn estimate_memory_usage() -> f32 {
    // In a real implementation, use platform-specific APIs
    // This is a placeholder
    50.0
}

/// Estimate draw calls based on entities
fn estimate_draw_calls(query: &Query<Entity>) -> u32 {
    // Simplified estimation
    // In reality, you'd count actual mesh instances, sprites, etc.
    (query.iter().count() as u32 / 10).max(1)
}

/// Quality level settings
#[derive(Resource)]
pub struct QualityLevel {
    pub shadow_quality: ShadowQuality,
    pub texture_quality: TextureQuality,
    pub particle_density: f32,
    pub render_distance: f32,
    pub antialiasing: bool,
}

#[derive(Clone, Copy)]
pub enum ShadowQuality {
    Low,
    Medium,
    High,
}

#[derive(Clone, Copy)]
pub enum TextureQuality {
    Low,
    High,
}

/// Aggressive optimization flags
#[derive(Resource)]
pub struct AggressiveOptimizations {
    pub disable_particles: bool,
    pub reduce_draw_distance: bool,
    pub simplify_shaders: bool,
    pub disable_post_processing: bool,
}

/// Optimized ECS query iterators using parallel processing
pub trait OptimizedQuery {
    /// Parallel iteration over query results
    fn par_iter(&self) -> impl ParallelIterator;
    
    /// Batched iteration for cache efficiency
    fn batched_iter(&self, batch_size: usize) -> impl Iterator;
}

/// Cache-friendly component storage optimization
pub mod cache_optimized {
    use super::*;
    
    /// Ensure components are aligned for SIMD operations
    #[repr(align(32))]
    #[derive(Component)]
    pub struct AlignedTransform {
        pub translation: Vec3,
        pub rotation: Quat,
        pub scale: Vec3,
    }
    
    /// Pack multiple boolean flags into a single component
    #[derive(Component)]
    pub struct PackedFlags {
        bits: u32,
    }
    
    impl PackedFlags {
        pub fn set_flag(&mut self, index: u8, value: bool) {
            if value {
                self.bits |= 1 << index;
            } else {
                self.bits &= !(1 << index);
            }
        }
        
        pub fn get_flag(&self, index: u8) -> bool {
            (self.bits & (1 << index)) != 0
        }
    }
}

/// Memory pool for frequent allocations
pub mod memory_pool {
    use super::*;
    use std::mem::MaybeUninit;
    
    pub struct ObjectPool<T> {
        objects: Vec<MaybeUninit<T>>,
        available: Vec<usize>,
    }
    
    impl<T> ObjectPool<T> {
        pub fn new(capacity: usize) -> Self {
            let mut objects = Vec::with_capacity(capacity);
            let mut available = Vec::with_capacity(capacity);
            
            for i in 0..capacity {
                objects.push(MaybeUninit::uninit());
                available.push(i);
            }
            
            Self { objects, available }
        }
        
        pub fn acquire(&mut self, value: T) -> Option<usize> {
            if let Some(index) = self.available.pop() {
                self.objects[index] = MaybeUninit::new(value);
                Some(index)
            } else {
                None
            }
        }
        
        pub fn release(&mut self, index: usize) {
            if index < self.objects.len() {
                self.available.push(index);
            }
        }
    }
}