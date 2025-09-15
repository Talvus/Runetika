// Android JNI Bridge Module
// Provides safe interop between Rust/Bevy and Android/Kotlin

pub mod jni_bridge;
pub mod event_handler;
pub mod asset_loader;
pub mod surface_renderer;
pub mod lifecycle;
pub mod logging;
pub mod memory;
pub mod kotlin_interface;

pub use jni_bridge::*;
pub use event_handler::*;
pub use asset_loader::*;
pub use surface_renderer::*;
pub use lifecycle::*;
pub use logging::*;
pub use memory::*;