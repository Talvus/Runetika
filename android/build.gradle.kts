// Gradle build configuration for Runetika Android
plugins {
    id("com.android.library")
    id("org.jetbrains.kotlin.android")
    id("org.mozilla.rust-android-gradle.rust-android")
}

android {
    namespace = "com.runetika.android"
    compileSdk = 34

    defaultConfig {
        minSdk = 24
        targetSdk = 34

        testInstrumentationRunner = "androidx.test.runner.AndroidJUnitRunner"
        consumerProguardFiles("consumer-rules.pro")

        // Configure NDK
        ndk {
            abiFilters += listOf("armeabi-v7a", "arm64-v8a", "x86", "x86_64")
        }
    }

    buildTypes {
        release {
            isMinifyEnabled = false
            proguardFiles(
                getDefaultProguardFile("proguard-android-optimize.txt"),
                "proguard-rules.pro"
            )
        }
    }

    compileOptions {
        sourceCompatibility = JavaVersion.VERSION_17
        targetCompatibility = JavaVersion.VERSION_17
    }

    kotlinOptions {
        jvmTarget = "17"
    }

    // Configure external native build
    externalNativeBuild {
        cmake {
            path = file("src/main/cpp/CMakeLists.txt")
            version = "3.22.1"
        }
    }

    // Source sets for Kotlin files
    sourceSets {
        getByName("main") {
            java.srcDirs("src/main/kotlin")
        }
    }
}

// Rust Android configuration
cargo {
    module = "../"  // Path to Rust project root
    libname = "runetika"
    targets = listOf("arm", "arm64", "x86", "x86_64")
    
    profile = "release"
    
    // Features to enable for Android build
    features = listOf()
    
    // Environment variables for build
    exec = { spec, target ->
        spec.environment("ANDROID_HOME", android.sdkDirectory.absolutePath)
        spec.environment("NDK_HOME", android.ndkDirectory.absolutePath)
    }
}

dependencies {
    implementation("androidx.core:core-ktx:1.12.0")
    implementation("androidx.appcompat:appcompat:1.6.1")
    implementation("com.google.android.material:material:1.11.0")
    
    // Coroutines for async operations
    implementation("org.jetbrains.kotlinx:kotlinx-coroutines-android:1.7.3")
    
    // Testing
    testImplementation("junit:junit:4.13.2")
    androidTestImplementation("androidx.test.ext:junit:1.1.5")
    androidTestImplementation("androidx.test.espresso:espresso-core:3.5.1")
}

// Task to build Rust library
tasks.register("buildRustLibrary") {
    doLast {
        exec {
            workingDir = file("../")
            commandLine("cargo", "build", "--target", "aarch64-linux-android", "--release")
        }
        exec {
            workingDir = file("../")
            commandLine("cargo", "build", "--target", "armv7-linux-androideabi", "--release")
        }
        exec {
            workingDir = file("../")
            commandLine("cargo", "build", "--target", "i686-linux-android", "--release")
        }
        exec {
            workingDir = file("../")
            commandLine("cargo", "build", "--target", "x86_64-linux-android", "--release")
        }
    }
}

// Copy built libraries to JNI folder
tasks.register("copyRustLibraries") {
    dependsOn("buildRustLibrary")
    doLast {
        copy {
            from("../target/aarch64-linux-android/release/librunetika.so")
            into("src/main/jniLibs/arm64-v8a/")
        }
        copy {
            from("../target/armv7-linux-androideabi/release/librunetika.so")
            into("src/main/jniLibs/armeabi-v7a/")
        }
        copy {
            from("../target/i686-linux-android/release/librunetika.so")
            into("src/main/jniLibs/x86/")
        }
        copy {
            from("../target/x86_64-linux-android/release/librunetika.so")
            into("src/main/jniLibs/x86_64/")
        }
    }
}

// Hook into the build process
tasks.preBuild {
    dependsOn("copyRustLibraries")
}