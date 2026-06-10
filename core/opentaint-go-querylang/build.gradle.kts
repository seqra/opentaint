import OpentaintIrDependency.opentaint_ir_api_go
import OpentaintIrDependency.opentaint_ir_core_go
import OpentaintUtilDependency.opentaintUtilJvm
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile
import org.opentaint.common.JunitDependencies
import org.opentaint.common.KotlinDependency
import org.opentaint.common.ensureGoEnvInitialized
import org.opentaint.common.goEnvironment

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
    implementation("org.opentaint.opentaint-dataflow-core:opentaint-go-dataflow")
    implementation("org.opentaint.opentaint-configuration-rules:configuration-rules-jvm")
    implementation("org.opentaint.opentaint-configuration-rules:configuration-rules-go")
    implementation(KotlinDependency.Libs.kotlin_logging)
    antlr(Libs.antlr)
    implementation(Libs.antlr_runtime)
    testImplementation(kotlin("test"))
    testImplementation(JunitDependencies.Libs.junit_jupiter)
    testImplementation(JunitDependencies.Libs.junit_jupiter_params)

    testImplementation(opentaint_ir_api_go)
    testImplementation(opentaint_ir_core_go)
    testImplementation(opentaintUtilJvm)
    testImplementation("org.opentaint.sast:dataflow")
    testImplementation("org.opentaint.config:go-config")
    testRuntimeOnly(Libs.logback)
}

val antlrPkg = "org.opentaint.semgrep.pattern.go.antlr"
val antlrPkgPath = antlrPkg.replace('.', '/')

val grammarUpstreamDir = layout.buildDirectory.dir("grammar/upstream")
val grammarPatchedDir = layout.buildDirectory.dir("grammar/patched")
val grammarJavaDir = layout.buildDirectory.dir("grammar/java/$antlrPkgPath")
// Pinned to a specific commit so the patch keeps applying cleanly.
val grammarCommitSha = "284602b3f23ca54dc30778204ab7ae9e969145e9"
val grammarBaseUrl = "https://raw.githubusercontent.com/antlr/grammars-v4/$grammarCommitSha/golang"
val grammarPatchFile = layout.projectDirectory.file("grammar/semgrep-extensions.patch")

val downloadGoGrammar by tasks.registering {
    inputs.property("commitSha", grammarCommitSha)
    inputs.property("baseUrl", grammarBaseUrl)
    outputs.dir(grammarUpstreamDir)
    outputs.dir(grammarJavaDir)
    doLast {
        val upstream = grammarUpstreamDir.get().asFile.apply { mkdirs() }
        listOf("GoLexer.g4", "GoParser.g4").forEach { f ->
            val target = upstream.resolve(f)
            uri("$grammarBaseUrl/$f").toURL().openStream().use { input ->
                target.outputStream().use { input.copyTo(it) }
            }
        }
        val javaDir = grammarJavaDir.get().asFile.apply { mkdirs() }
        val baseFile = javaDir.resolve("GoParserBase.java")
        val content = uri("$grammarBaseUrl/Java/GoParserBase.java").toURL().readText()
        baseFile.writeText("package $antlrPkg;\n$content")
    }
}

val patchGoGrammar by tasks.registering {
    dependsOn(downloadGoGrammar)
    inputs.dir(grammarUpstreamDir)
    inputs.file(grammarPatchFile)
    outputs.dir(grammarPatchedDir)
    doLast {
        val patched = grammarPatchedDir.get().asFile
        val upstream = grammarUpstreamDir.get().asFile
        patched.deleteRecursively()
        patched.mkdirs()
        listOf("GoLexer.g4", "GoParser.g4").forEach { f ->
            upstream.resolve(f).copyTo(patched.resolve(f), overwrite = true)
        }
        val result = exec {
            workingDir = patched
            commandLine(
                "patch",
                "--no-backup-if-mismatch",
                "-p1",
                "-i", grammarPatchFile.asFile.absolutePath,
            )
            isIgnoreExitValue = true
        }
        if (result.exitValue != 0) {
            throw GradleException("Failed to apply ${grammarPatchFile.asFile} (exit ${result.exitValue})")
        }
    }
}

sourceSets {
    main {
        java.srcDir(layout.buildDirectory.dir("grammar/java"))
        antlr.setSrcDirs(listOf(grammarPatchedDir))
    }
}

tasks.generateGrammarSource {
    dependsOn(patchGoGrammar)
    arguments = arguments + listOf("-package", antlrPkg, "-visitor")
    outputDirectory = outputDirectory.resolve(antlrPkgPath)
}

tasks.withType<JavaCompile> {
    options.compilerArgs.remove("-Werror")
    sourceCompatibility = JavaVersion.VERSION_11.toString()
    targetCompatibility = JavaVersion.VERSION_11.toString()
    dependsOn(downloadGoGrammar)
}

tasks.withType<KotlinCompile> {
    kotlinOptions.jvmTarget = "11"
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

    systemProperty("GO_SAMPLES_DIR", layout.projectDirectory.dir("samples-go").asFile.absolutePath)
    systemProperty("GO_MASSIVE_SAMPLES_DIR", layout.projectDirectory.dir("samples-go-massive").asFile.absolutePath)
    systemProperty("GO_MASSIVE_OUTPUT_DIR", layout.buildDirectory.dir("go-massive-report").get().asFile.absolutePath)
    ensureGoEnvInitialized()
    doFirst {
        goEnvironment().forEach { (key, value) -> environment(key, value) }
    }
}