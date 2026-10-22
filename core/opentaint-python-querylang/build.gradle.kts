import OpentaintIrDependency.opentaint_ir_api_python
import OpentaintIrDependency.opentaint_ir_core_python
import OpentaintUtilDependency.opentaintUtilJvm
import org.jetbrains.kotlin.gradle.dsl.JvmTarget
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile
import org.opentaint.common.JunitDependencies
import org.opentaint.common.KotlinDependency
import org.opentaint.common.ensurePirEnvInitialized
import org.opentaint.common.pirEnvironment

plugins {
    id("kotlin-conventions")
    antlr
}

// workaround to remove antlr grammar generation dependencies from runtime classpath
configurations.api.get().let { config ->
    config.setExtendsFrom(config.extendsFrom.filterNot { it == configurations.antlr.get() })
}

dependencies {
    implementation(project(":opentaint-java-querylang"))
    implementation("org.opentaint.opentaint-dataflow-core:opentaint-python-dataflow")
    implementation("org.opentaint.opentaint-configuration-rules:configuration-rules-jvm")
    implementation("org.opentaint.opentaint-configuration-rules:configuration-rules-python")
    implementation(KotlinDependency.Libs.kotlin_logging)
    antlr(Libs.antlr)
    implementation(Libs.antlr_runtime)
    testImplementation(kotlin("test"))
    testImplementation(JunitDependencies.Libs.junit_jupiter)
    testImplementation(JunitDependencies.Libs.junit_jupiter_params)

    testImplementation(opentaint_ir_api_python)
    testImplementation(opentaint_ir_core_python)
    testImplementation(opentaintUtilJvm)
    testImplementation("org.opentaint.sast:dataflow")
    testImplementation("org.opentaint.config:python-config")
    testRuntimeOnly(Libs.logback)
}

val antlrPkg = "org.opentaint.semgrep.pattern.python.antlr"
val antlrPkgPath = antlrPkg.replace('.', '/')

val grammarUpstreamDir = layout.buildDirectory.dir("grammar/upstream")
val grammarPatchedDir = layout.buildDirectory.dir("grammar/patched")
val grammarJavaDir = layout.buildDirectory.dir("grammar/java/")

// Pinned to a specific commit so the patch keeps applying cleanly.
val grammarCommitSha = "b8da12293f626bc561e5c05c4011f5b5b5e778a8"
val grammarBaseUrl = "https://raw.githubusercontent.com/antlr/grammars-v4/$grammarCommitSha/python/python3_14"
val grammarPatchFile = layout.projectDirectory.file("grammar/semgrep-extensions.patch")

val downloadPythonGrammar by tasks.registering {
    inputs.property("commitSha", grammarCommitSha)
    inputs.property("baseUrl", grammarBaseUrl)
    outputs.dir(grammarUpstreamDir)
    outputs.dir(grammarJavaDir)
    doLast {
        val upstream = grammarUpstreamDir.get().asFile.apply { mkdirs() }
        listOf("PythonLexer.g4", "PythonParser.g4").forEach { f ->
            val target = upstream.resolve(f)
            uri("$grammarBaseUrl/$f").toURL().openStream().use { input ->
                target.outputStream().use { input.copyTo(it) }
            }
        }
        val javaDir = grammarJavaDir.get().asFile.resolve(antlrPkgPath).apply { mkdirs() }
        val baseFile = javaDir.resolve("PythonLexerBase.java")
        val content = uri("$grammarBaseUrl/Java/PythonLexerBase.java").toURL().readText()
        baseFile.writeText("package $antlrPkg;\n$content")
    }
}

val patchPythonGrammar by tasks.registering {
    dependsOn(downloadPythonGrammar)
    inputs.dir(grammarUpstreamDir)
    inputs.file(grammarPatchFile)
    outputs.dir(grammarPatchedDir)
    doLast {
        applyPatch(
            upstream = grammarUpstreamDir.get().asFile,
            patched = grammarPatchedDir.get().asFile,
            files = listOf("PythonLexer.g4", "PythonParser.g4"),
            patchFile = grammarPatchFile.asFile
        )
    }
}

fun applyPatch(upstream: File, patched: File, files: List<String>, patchFile: File) {
    patched.deleteRecursively()
    patched.mkdirs()
    files.forEach { f ->
        upstream.resolve(f).copyTo(patched.resolve(f), overwrite = true)
    }
    val result = exec {
        workingDir = patched
        commandLine(
            "patch",
            "--no-backup-if-mismatch",
            "-p1",
            "-i", patchFile.absolutePath,
        )
        isIgnoreExitValue = true
    }
    if (result.exitValue != 0) {
        throw GradleException("Failed to apply $patchFile (exit ${result.exitValue})")
    }
}


sourceSets {
    main {
        java.srcDir(grammarJavaDir)
        antlr.setSrcDirs(listOf(grammarPatchedDir))
    }
}

tasks.generateGrammarSource {
    dependsOn(patchPythonGrammar)
    arguments = arguments + listOf("-package", antlrPkg, "-visitor")
    outputDirectory = outputDirectory.resolve(antlrPkgPath)
}

tasks.withType<JavaCompile> {
    options.compilerArgs.remove("-Werror")
    dependsOn(downloadPythonGrammar)
}

tasks.named<JavaCompile>("compileTestJava") {
    sourceCompatibility = JavaVersion.VERSION_17.toString()
    targetCompatibility = JavaVersion.VERSION_17.toString()
}

tasks.named<KotlinCompile>("compileTestKotlin") {
    compilerOptions {
        jvmTarget = JvmTarget.JVM_17
    }
}

tasks.compileKotlin {
    dependsOn(tasks.generateGrammarSource)
}

tasks.compileTestKotlin {
    dependsOn(tasks.generateTestGrammarSource)
}

tasks.withType<Test> {
    useJUnitPlatform()
    jvmArgs = listOf("-Xmx8g")

    systemProperty("PY_SAMPLES_DIR", layout.projectDirectory.dir("samples-py").asFile.absolutePath)
    ensurePirEnvInitialized()
    doFirst {
        pirEnvironment().forEach { (key, value) -> environment(key, value) }
    }
}
