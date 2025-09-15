#!/bin/bash

# Build script for Runetika Android
# Compiles Rust library for all Android architectures

set -e

echo "🚀 Building Runetika for Android"

# Check prerequisites
if [ -z "$ANDROID_HOME" ]; then
    echo "❌ Error: ANDROID_HOME not set"
    echo "Please set ANDROID_HOME to your Android SDK path"
    exit 1
fi

if [ -z "$NDK_HOME" ]; then
    # Try to find NDK in standard location
    NDK_HOME="$ANDROID_HOME/ndk/25.2.9519653"
    if [ ! -d "$NDK_HOME" ]; then
        echo "❌ Error: NDK_HOME not set and NDK not found at $NDK_HOME"
        echo "Please install Android NDK or set NDK_HOME"
        exit 1
    fi
fi

echo "📱 Android SDK: $ANDROID_HOME"
echo "🔧 Android NDK: $NDK_HOME"

# Install Rust targets if not already installed
echo "📦 Checking Rust Android targets..."
rustup target add aarch64-linux-android || true
rustup target add armv7-linux-androideabi || true
rustup target add i686-linux-android || true
rustup target add x86_64-linux-android || true

# Set up cargo config for Android
mkdir -p .cargo
cat > .cargo/config.toml << EOF
[target.aarch64-linux-android]
linker = "$NDK_HOME/toolchains/llvm/prebuilt/darwin-x86_64/bin/aarch64-linux-android24-clang"

[target.armv7-linux-androideabi]
linker = "$NDK_HOME/toolchains/llvm/prebuilt/darwin-x86_64/bin/armv7a-linux-androideabi24-clang"

[target.i686-linux-android]
linker = "$NDK_HOME/toolchains/llvm/prebuilt/darwin-x86_64/bin/i686-linux-android24-clang"

[target.x86_64-linux-android]
linker = "$NDK_HOME/toolchains/llvm/prebuilt/darwin-x86_64/bin/x86_64-linux-android24-clang"
EOF

# Build for each architecture
echo "🏗️ Building for ARM64..."
cargo build --target aarch64-linux-android --release --lib

echo "🏗️ Building for ARMv7..."
cargo build --target armv7-linux-androideabi --release --lib

echo "🏗️ Building for x86..."
cargo build --target i686-linux-android --release --lib

echo "🏗️ Building for x86_64..."
cargo build --target x86_64-linux-android --release --lib

# Create JNI libs directory structure
echo "📂 Setting up JNI libraries..."
mkdir -p android/src/main/jniLibs/arm64-v8a
mkdir -p android/src/main/jniLibs/armeabi-v7a
mkdir -p android/src/main/jniLibs/x86
mkdir -p android/src/main/jniLibs/x86_64

# Copy built libraries
echo "📋 Copying libraries..."
cp target/aarch64-linux-android/release/librunetika.so android/src/main/jniLibs/arm64-v8a/ || true
cp target/armv7-linux-androideabi/release/librunetika.so android/src/main/jniLibs/armeabi-v7a/ || true
cp target/i686-linux-android/release/librunetika.so android/src/main/jniLibs/x86/ || true
cp target/x86_64-linux-android/release/librunetika.so android/src/main/jniLibs/x86_64/ || true

# Strip debug symbols for smaller size
echo "🔨 Stripping debug symbols..."
"$NDK_HOME/toolchains/llvm/prebuilt/darwin-x86_64/bin/llvm-strip" android/src/main/jniLibs/arm64-v8a/librunetika.so || true
"$NDK_HOME/toolchains/llvm/prebuilt/darwin-x86_64/bin/llvm-strip" android/src/main/jniLibs/armeabi-v7a/librunetika.so || true
"$NDK_HOME/toolchains/llvm/prebuilt/darwin-x86_64/bin/llvm-strip" android/src/main/jniLibs/x86/librunetika.so || true
"$NDK_HOME/toolchains/llvm/prebuilt/darwin-x86_64/bin/llvm-strip" android/src/main/jniLibs/x86_64/librunetika.so || true

# Show library sizes
echo "📊 Library sizes:"
ls -lh android/src/main/jniLibs/arm64-v8a/librunetika.so 2>/dev/null || echo "  ARM64: Not built"
ls -lh android/src/main/jniLibs/armeabi-v7a/librunetika.so 2>/dev/null || echo "  ARMv7: Not built"
ls -lh android/src/main/jniLibs/x86/librunetika.so 2>/dev/null || echo "  x86: Not built"
ls -lh android/src/main/jniLibs/x86_64/librunetika.so 2>/dev/null || echo "  x86_64: Not built"

echo "✅ Android build complete!"
echo ""
echo "Next steps:"
echo "1. cd android"
echo "2. ./gradlew assembleDebug  # Build debug APK"
echo "3. ./gradlew installDebug   # Install on connected device"