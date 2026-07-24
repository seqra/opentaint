plugins {
    java
}

tasks {
    withType<JavaCompile> {
        // Java 17 (was 1.8) so record samples compile: records lower equals/
        // hashCode/toString to invokedynamic bootstrapped by
        // java.lang.runtime.ObjectMethods, which RecordAliasSample exercises to
        // pin the arity guard in resolveCallNoCache. Existing samples use no
        // invokedynamic constructs, so their bytecode shape is unchanged.
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
