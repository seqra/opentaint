import org.gradle.api.tasks.testing.Test
import java.io.File

plugins {
    id("kotlin-conventions")
}

val pirProject = project(":python")
val pirRootDir = pirProject.layout.projectDirectory
val pirServerPython = pirRootDir.file(".venv/bin/python").asFile.absolutePath
val inheritedPythonPath = providers.environmentVariable("PYTHONPATH").orNull
val pirPythonPath = listOfNotNull(
    pirRootDir.asFile.absolutePath,
    inheritedPythonPath,
).filter { it.isNotBlank() }.joinToString(File.pathSeparator)

tasks.withType<Test>().configureEach {
    dependsOn(":python:generatePirProtoStubs")

    inputs.files(
        pirProject.fileTree("pir_server") {
            include("**/*.py")
            include("**/*.proto")
        },
        pirRootDir.file("pyproject.toml"),
    )

    environment("PIR_SERVER_PYTHON", pirServerPython)
    environment("PYTHONPATH", pirPythonPath)

    testLogging {
        events("started", "passed", "failed", "skipped")
        showStandardStreams = false
        showExceptions = true
        showCauses = true
        showStackTraces = true
        exceptionFormat = org.gradle.api.tasks.testing.logging.TestExceptionFormat.FULL
    }
}

dependencies {
    testImplementation(project(":python:opentaint-ir-api-python"))
    testImplementation(project(":python:opentaint-ir-impl-python"))

    testImplementation("com.google.code.gson:gson:2.10.1")

    // Needed for Tier 3 round-trip tests (ExecuteFunctionRequest/Response)
    testImplementation("com.google.protobuf:protobuf-java:4.29.3")
    testImplementation("io.grpc:grpc-protobuf:1.69.0")
    testImplementation("io.grpc:grpc-stub:1.69.0")
}

tasks.test {
    useJUnitPlatform {
        excludeTags("tier1")
    }
    maxParallelForks = 4
    maxHeapSize = "2g"
}

val testSourceSet = sourceSets["test"]

tasks.register<Test>("benchmarkTest") {
    group = "verification"
    description = "Runs the Tier-1 benchmarks over installed packages and cloned web projects."
    testClassesDirs = testSourceSet.output.classesDirs
    classpath = testSourceSet.runtimeClasspath
    useJUnitPlatform {
        includeTags("tier1")
    }
    dependsOn(":python:setupPirBenchmarkDeps")
    dependsOn(setupWebProjects)
    systemProperty("WEB_PROJECTS_DIR", webProjectsDir)
    maxParallelForks = 2
    maxHeapSize = "8g"
    testLogging {
        showStandardStreams = true
    }
}

// ─── Web project setup for Tier-1 benchmarks ──────────────────────

val webProjectsDir = project.findProperty("pir.webprojects.dir")?.toString()
    ?: layout.buildDirectory.dir("web-projects").get().asFile.absolutePath
val webProjectsManifest = layout.projectDirectory.file("web-projects.txt")

fun exec(vararg args: String, dir: File? = null): Pair<Int, String> {
    val pb = ProcessBuilder(*args).redirectErrorStream(true)
    if (dir != null) pb.directory(dir)
    val proc = pb.start()
    val output = proc.inputStream.bufferedReader().readText()
    return proc.waitFor() to output.trim()
}

fun run(vararg args: String, dir: File? = null) {
    val (rc, output) = exec(*args, dir = dir)
    output.lineSequence().forEach { println("  $it") }
    if (rc != 0) {
        throw GradleException("Command failed (exit $rc): ${args.joinToString(" ")}")
    }
}

val setupWebProjects = tasks.register("setupWebProjects") {
    group = "benchmark"
    description = "Clone and checkout web projects listed in web-projects.txt at pinned commits."

    doLast {
        val entries = webProjectsManifest.asFile.readLines()
            .map { it.trim() }
            .filter { it.isNotEmpty() && !it.startsWith("#") }
            .map { line ->
                val parts = line.split("|")
                check(parts.size == 3) { "Bad line in web-projects.txt: $line" }
                Triple(parts[0], parts[1], parts[2])
            }

        println("Setting up ${entries.size} web projects")

        for ((name, commit, url) in entries) {
            val projectDir = File(webProjectsDir, name)
            if (projectDir.exists()) {
                val (rc, head) = exec("git", "rev-parse", "HEAD", dir = projectDir)
                if (rc == 0 && head == commit) {
                    println("[$name] Already at $commit")
                    continue
                }
                println("[$name] Already exists, checking out $commit")
                run("git", "fetch", "--depth=1", "origin", commit, dir = projectDir)
                run("git", "checkout", commit, dir = projectDir)
            } else {
                println("[$name] Cloning $url @ $commit")
                run("git", "clone", "--depth=1", url, projectDir.absolutePath)
                run("git", "fetch", "--depth=1", "origin", commit, dir = projectDir)
                run("git", "checkout", commit, dir = projectDir)
            }
        }

        println("Done: ${entries.size} web projects ready.")
    }
}
