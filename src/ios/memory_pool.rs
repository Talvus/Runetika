//! Memory pool management for iOS with aggressive memory reuse
//! 
//! Implements custom memory pools, arena allocators, and zero-copy strategies
//! to keep memory usage under 50MB.

use bevy::prelude::*;
use std::sync::{Arc, Mutex};
use std::collections::HashMap;

/// Memory pool plugin
pub struct MemoryPoolPlugin;

impl Plugin for MemoryPoolPlugin {
    fn build(&self, app: &mut App) {
        app
            .init_resource::<GlobalMemoryPool>()
            .init_resource::<TextureMemoryPool>()
            .init_resource::<MeshMemoryPool>()
            .init_resource::<UniformBufferPool>()
            .add_systems(PreStartup, initialize_memory_pools)
            .add_systems(PreUpdate, update_memory_pressure)
            .add_systems(PostUpdate, (
                compact_memory_pools,
                reclaim_unused_memory,
            ));
    }
}

/// Global memory pool manager
#[derive(Resource)]
pub struct GlobalMemoryPool {
    /// Total allocated memory across all pools
    pub total_allocated_bytes: usize,
    /// Memory limit in bytes
    pub memory_limit_bytes: usize,
    /// Current memory pressure level
    pub pressure_level: MemoryPressure,
    /// Pool statistics
    pub stats: PoolStatistics,
    /// Emergency reserve pool
    pub emergency_pool: Arc<Mutex<Vec<u8>>>,
}

impl Default for GlobalMemoryPool {
    fn default() -> Self {
        Self {
            total_allocated_bytes: 0,
            memory_limit_bytes: 50 * 1024 * 1024, // 50MB limit
            pressure_level: MemoryPressure::Low,
            stats: PoolStatistics::default(),
            emergency_pool: Arc::new(Mutex::new(Vec::with_capacity(1024 * 1024))), // 1MB emergency
        }
    }
}

/// Memory pressure levels
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum MemoryPressure {
    /// Plenty of memory available
    Low,
    /// Should start being careful
    Medium,
    /// Need to free memory
    High,
    /// Critical - immediate action needed
    Critical,
}

/// Pool statistics for monitoring
#[derive(Default, Debug)]
pub struct PoolStatistics {
    /// Total allocations
    pub total_allocations: u64,
    /// Total deallocations
    pub total_deallocations: u64,
    /// Current active allocations
    pub active_allocations: u64,
    /// Peak memory usage
    pub peak_memory_bytes: usize,
    /// Fragmentation ratio (0.0 - 1.0)
    pub fragmentation: f32,
    /// Cache hit rate
    pub cache_hit_rate: f32,
}

/// Texture memory pool with ASTC compression support
#[derive(Resource)]
pub struct TextureMemoryPool {
    /// Memory blocks organized by size
    pub blocks: HashMap<TextureSize, Vec<TextureBlock>>,
    /// Free list for each size
    pub free_lists: HashMap<TextureSize, Vec<usize>>,
    /// Compressed texture cache
    pub compressed_cache: HashMap<u64, CompressedTextureData>,
    /// Total texture memory
    pub total_bytes: usize,
    /// Maximum texture memory
    pub max_bytes: usize,
}

impl Default for TextureMemoryPool {
    fn default() -> Self {
        Self {
            blocks: HashMap::new(),
            free_lists: HashMap::new(),
            compressed_cache: HashMap::new(),
            total_bytes: 0,
            max_bytes: 20 * 1024 * 1024, // 20MB for textures
        }
    }
}

/// Texture size categories
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub enum TextureSize {
    /// 64x64 textures
    Tiny,
    /// 128x128 textures
    Small,
    /// 256x256 textures
    Medium,
    /// 512x512 textures
    Large,
    /// 1024x1024 textures
    XLarge,
    /// 2048x2048 textures
    XXLarge,
}

impl TextureSize {
    /// Get byte size for this texture size
    pub fn byte_size(&self) -> usize {
        match self {
            Self::Tiny => 64 * 64 * 4,      // 16KB
            Self::Small => 128 * 128 * 4,    // 64KB
            Self::Medium => 256 * 256 * 4,   // 256KB
            Self::Large => 512 * 512 * 4,    // 1MB
            Self::XLarge => 1024 * 1024 * 4, // 4MB
            Self::XXLarge => 2048 * 2048 * 4, // 16MB
        }
    }
    
    /// Get ASTC compressed size (approximately 25% of original)
    pub fn compressed_size(&self) -> usize {
        self.byte_size() / 4
    }
}

/// Texture memory block
pub struct TextureBlock {
    /// Block ID
    pub id: usize,
    /// Size category
    pub size: TextureSize,
    /// Memory buffer
    pub buffer: Arc<Vec<u8>>,
    /// Is currently in use
    pub in_use: bool,
    /// Last access time
    pub last_access: std::time::Instant,
    /// Reference count
    pub ref_count: u32,
}

/// Compressed texture data
pub struct CompressedTextureData {
    /// Original texture ID
    pub texture_id: u64,
    /// Compressed data
    pub data: Arc<Vec<u8>>,
    /// Compression format
    pub format: CompressionFormat,
    /// Original dimensions
    pub width: u32,
    pub height: u32,
    /// Compression ratio
    pub ratio: f32,
}

/// Compression formats
#[derive(Clone, Copy, Debug)]
pub enum CompressionFormat {
    /// ASTC 4x4
    ASTC4x4,
    /// ASTC 6x6
    ASTC6x6,
    /// ASTC 8x8
    ASTC8x8,
    /// PVRTC 4bpp
    PVRTC4,
    /// Raw (uncompressed)
    Raw,
}

/// Mesh memory pool
#[derive(Resource)]
pub struct MeshMemoryPool {
    /// Vertex buffer pools
    pub vertex_pools: Vec<BufferPool>,
    /// Index buffer pools
    pub index_pools: Vec<BufferPool>,
    /// Instance buffer pools
    pub instance_pools: Vec<BufferPool>,
    /// Total mesh memory
    pub total_bytes: usize,
    /// Maximum mesh memory
    pub max_bytes: usize,
}

impl Default for MeshMemoryPool {
    fn default() -> Self {
        Self {
            vertex_pools: vec![
                BufferPool::new(1024),     // 1KB buffers
                BufferPool::new(4096),     // 4KB buffers
                BufferPool::new(16384),    // 16KB buffers
                BufferPool::new(65536),    // 64KB buffers
            ],
            index_pools: vec![
                BufferPool::new(512),      // 512B buffers
                BufferPool::new(2048),     // 2KB buffers
                BufferPool::new(8192),     // 8KB buffers
            ],
            instance_pools: vec![
                BufferPool::new(256),      // 256B buffers
                BufferPool::new(1024),     // 1KB buffers
            ],
            total_bytes: 0,
            max_bytes: 10 * 1024 * 1024, // 10MB for meshes
        }
    }
}

/// Generic buffer pool
pub struct BufferPool {
    /// Buffer size for this pool
    pub buffer_size: usize,
    /// Available buffers
    pub available: Vec<Arc<Vec<u8>>>,
    /// In-use buffers
    pub in_use: Vec<Arc<Vec<u8>>>,
    /// High water mark
    pub high_water_mark: usize,
}

impl BufferPool {
    /// Create a new buffer pool
    pub fn new(buffer_size: usize) -> Self {
        Self {
            buffer_size,
            available: Vec::new(),
            in_use: Vec::new(),
            high_water_mark: 0,
        }
    }
    
    /// Allocate a buffer from the pool
    pub fn allocate(&mut self) -> Arc<Vec<u8>> {
        if let Some(buffer) = self.available.pop() {
            self.in_use.push(buffer.clone());
            buffer
        } else {
            // Create new buffer
            let buffer = Arc::new(vec![0u8; self.buffer_size]);
            self.in_use.push(buffer.clone());
            self.high_water_mark = self.high_water_mark.max(self.in_use.len());
            buffer
        }
    }
    
    /// Return a buffer to the pool
    pub fn deallocate(&mut self, buffer: Arc<Vec<u8>>) {
        if let Some(index) = self.in_use.iter().position(|b| Arc::ptr_eq(b, &buffer)) {
            self.in_use.remove(index);
            self.available.push(buffer);
        }
    }
    
    /// Compact the pool by removing excess buffers
    pub fn compact(&mut self) {
        // Keep only as many buffers as the high water mark
        while self.available.len() > self.high_water_mark {
            self.available.pop();
        }
    }
}

/// Uniform buffer pool for shader constants
#[derive(Resource)]
pub struct UniformBufferPool {
    /// Small uniform buffers (< 256 bytes)
    pub small_buffers: BufferPool,
    /// Medium uniform buffers (256 - 1024 bytes)
    pub medium_buffers: BufferPool,
    /// Large uniform buffers (> 1024 bytes)
    pub large_buffers: BufferPool,
    /// Ring buffer for streaming uniforms
    pub streaming_buffer: StreamingBuffer,
}

impl Default for UniformBufferPool {
    fn default() -> Self {
        Self {
            small_buffers: BufferPool::new(256),
            medium_buffers: BufferPool::new(1024),
            large_buffers: BufferPool::new(4096),
            streaming_buffer: StreamingBuffer::new(1024 * 1024), // 1MB streaming buffer
        }
    }
}

/// Streaming buffer for dynamic uniforms
pub struct StreamingBuffer {
    /// Buffer memory
    pub buffer: Arc<Vec<u8>>,
    /// Current write position
    pub write_pos: usize,
    /// Buffer size
    pub size: usize,
    /// Frame markers for triple buffering
    pub frame_markers: [usize; 3],
    /// Current frame index
    pub frame_index: usize,
}

impl StreamingBuffer {
    /// Create a new streaming buffer
    pub fn new(size: usize) -> Self {
        Self {
            buffer: Arc::new(vec![0u8; size]),
            write_pos: 0,
            size,
            frame_markers: [0; 3],
            frame_index: 0,
        }
    }
    
    /// Allocate space in the streaming buffer
    pub fn allocate(&mut self, size: usize) -> Option<usize> {
        if self.write_pos + size > self.size {
            // Buffer full, need to wrap
            return None;
        }
        
        let offset = self.write_pos;
        self.write_pos += size;
        
        // Align to 16 bytes
        self.write_pos = (self.write_pos + 15) & !15;
        
        Some(offset)
    }
    
    /// Advance to next frame
    pub fn next_frame(&mut self) {
        self.frame_markers[self.frame_index] = self.write_pos;
        self.frame_index = (self.frame_index + 1) % 3;
        
        // Reset write position to after oldest frame
        self.write_pos = self.frame_markers[self.frame_index];
    }
}

// Memory pool systems

fn initialize_memory_pools(
    mut global_pool: ResMut<GlobalMemoryPool>,
    mut texture_pool: ResMut<TextureMemoryPool>,
    mut mesh_pool: ResMut<MeshMemoryPool>,
) {
    info!("Initializing iOS memory pools");
    
    // Pre-allocate texture blocks
    for size in [TextureSize::Tiny, TextureSize::Small, TextureSize::Medium] {
        let count = match size {
            TextureSize::Tiny => 20,   // 20 tiny textures
            TextureSize::Small => 10,  // 10 small textures
            TextureSize::Medium => 5,  // 5 medium textures
            _ => 0,
        };
        
        let mut blocks = Vec::new();
        let mut free_list = Vec::new();
        
        for i in 0..count {
            blocks.push(TextureBlock {
                id: i,
                size,
                buffer: Arc::new(vec![0u8; size.byte_size()]),
                in_use: false,
                last_access: std::time::Instant::now(),
                ref_count: 0,
            });
            free_list.push(i);
        }
        
        texture_pool.blocks.insert(size, blocks);
        texture_pool.free_lists.insert(size, free_list);
        texture_pool.total_bytes += size.byte_size() * count;
    }
    
    // Pre-allocate mesh buffers
    for pool in &mut mesh_pool.vertex_pools {
        for _ in 0..5 {
            pool.available.push(Arc::new(vec![0u8; pool.buffer_size]));
        }
        mesh_pool.total_bytes += pool.buffer_size * 5;
    }
    
    // Update global pool stats
    global_pool.total_allocated_bytes = texture_pool.total_bytes + mesh_pool.total_bytes;
    global_pool.stats.peak_memory_bytes = global_pool.total_allocated_bytes;
    
    info!("Memory pools initialized: {:.2} MB allocated", 
          global_pool.total_allocated_bytes as f32 / 1024.0 / 1024.0);
}

fn update_memory_pressure(
    mut global_pool: ResMut<GlobalMemoryPool>,
) {
    let usage_ratio = global_pool.total_allocated_bytes as f32 / 
                     global_pool.memory_limit_bytes as f32;
    
    global_pool.pressure_level = if usage_ratio < 0.5 {
        MemoryPressure::Low
    } else if usage_ratio < 0.75 {
        MemoryPressure::Medium
    } else if usage_ratio < 0.9 {
        MemoryPressure::High
    } else {
        MemoryPressure::Critical
    };
    
    if global_pool.pressure_level >= MemoryPressure::High {
        warn!("Memory pressure {:?}: {:.2} MB / {:.2} MB", 
              global_pool.pressure_level,
              global_pool.total_allocated_bytes as f32 / 1024.0 / 1024.0,
              global_pool.memory_limit_bytes as f32 / 1024.0 / 1024.0);
    }
}

fn compact_memory_pools(
    mut mesh_pool: ResMut<MeshMemoryPool>,
    mut texture_pool: ResMut<TextureMemoryPool>,
    global_pool: Res<GlobalMemoryPool>,
) {
    if global_pool.pressure_level < MemoryPressure::Medium {
        return;
    }
    
    // Compact mesh buffer pools
    for pool in &mut mesh_pool.vertex_pools {
        pool.compact();
    }
    for pool in &mut mesh_pool.index_pools {
        pool.compact();
    }
    
    // Evict old textures
    let now = std::time::Instant::now();
    let eviction_threshold = std::time::Duration::from_secs(10);
    
    for (_size, blocks) in texture_pool.blocks.iter_mut() {
        for block in blocks.iter_mut() {
            if !block.in_use && now.duration_since(block.last_access) > eviction_threshold {
                // Mark for eviction
                block.buffer = Arc::new(Vec::new());
            }
        }
    }
}

fn reclaim_unused_memory(
    mut global_pool: ResMut<GlobalMemoryPool>,
    texture_pool: Res<TextureMemoryPool>,
    mesh_pool: Res<MeshMemoryPool>,
) {
    if global_pool.pressure_level < MemoryPressure::High {
        return;
    }
    
    // Calculate current usage
    let current_usage = texture_pool.total_bytes + mesh_pool.total_bytes;
    
    // Update statistics
    global_pool.total_allocated_bytes = current_usage;
    global_pool.stats.active_allocations = 
        texture_pool.blocks.values().flatten().filter(|b| b.in_use).count() as u64;
    
    if global_pool.pressure_level == MemoryPressure::Critical {
        warn!("Critical memory pressure! Forcing garbage collection");
        // In a real implementation, this would trigger iOS memory warnings
    }
}

/// Memory allocation handle
pub struct MemoryHandle {
    /// Pool type
    pub pool: PoolType,
    /// Block ID
    pub block_id: usize,
    /// Offset within block
    pub offset: usize,
    /// Size
    pub size: usize,
}

/// Pool types
#[derive(Clone, Copy, Debug)]
pub enum PoolType {
    Texture,
    Vertex,
    Index,
    Instance,
    Uniform,
}

/// Zero-copy memory mapping
pub struct ZeroCopyMapping {
    /// Mapped memory pointer
    pub ptr: *mut u8,
    /// Size of mapping
    pub size: usize,
    /// Is currently mapped
    pub is_mapped: bool,
}

impl ZeroCopyMapping {
    /// Map memory for zero-copy access
    pub unsafe fn map(buffer: &Arc<Vec<u8>>, offset: usize, size: usize) -> Self {
        let ptr = buffer.as_ptr().add(offset) as *mut u8;
        Self {
            ptr,
            size,
            is_mapped: true,
        }
    }
    
    /// Unmap memory
    pub fn unmap(&mut self) {
        self.is_mapped = false;
        self.ptr = std::ptr::null_mut();
    }
}

/// Memory allocator interface
pub trait MemoryAllocator {
    /// Allocate memory
    fn allocate(&mut self, size: usize) -> Option<MemoryHandle>;
    
    /// Deallocate memory
    fn deallocate(&mut self, handle: MemoryHandle);
    
    /// Get current usage
    fn usage(&self) -> usize;
    
    /// Get maximum capacity
    fn capacity(&self) -> usize;
}