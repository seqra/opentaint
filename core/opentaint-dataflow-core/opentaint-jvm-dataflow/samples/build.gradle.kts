plugins {
    java
}

tasks {
    withType<JavaCompile> {
        // Records provide a real unresolved invokedynamic call site for the
        // alias-analysis samples. Existing samples remain source-compatible.
        sourceCompatibility = JavaVersion.VERSION_17.toString()
        targetCompatibility = JavaVersion.VERSION_17.toString()
        options.compilerArgs.add("-g")
    }
}

tasks.jar {
    from(sourceSets.main.get().allSource) {
        include("**/*.java")
    }
}
