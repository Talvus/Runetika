pluginManagement {
    repositories {
        google()
        mavenCentral()
        gradlePluginPortal()
    }
    
    plugins {
        id("com.android.library") version "8.2.0"
        id("org.jetbrains.kotlin.android") version "1.9.20"
        id("org.mozilla.rust-android-gradle.rust-android") version "0.9.3"
    }
}

dependencyResolutionManagement {
    repositoriesMode.set(RepositoriesMode.FAIL_ON_PROJECT_REPOS)
    repositories {
        google()
        mavenCentral()
    }
}

rootProject.name = "RunetikaAndroid"