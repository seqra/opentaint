plugins {
    java
}

val recordSamplePath = "sample/alias/RecordAliasSample.java"
val supportsJava17 = JavaVersion.current().isCompatibleWith(JavaVersion.VERSION_17)

sourceSets.main {
    java.exclude(recordSamplePath)
}

tasks {
    withType<JavaCompile> {
        sourceCompatibility = JavaVersion.VERSION_1_8.toString()
        targetCompatibility = JavaVersion.VERSION_1_8.toString()
        options.compilerArgs.add("-g")
    }
}

val java17 = sourceSets.create("java17") {
    java.setSrcDirs(listOf("src/main/java"))
    java.include(recordSamplePath)
}

tasks.named<JavaCompile>(java17.compileJavaTaskName) {
    enabled = supportsJava17
    sourceCompatibility = JavaVersion.VERSION_17.toString()
    targetCompatibility = JavaVersion.VERSION_17.toString()
}

tasks.jar {
    if (supportsJava17) {
        from(java17.output)
    }
    from(sourceSets.main.get().allSource) {
        include("**/*.java")
    }
}
