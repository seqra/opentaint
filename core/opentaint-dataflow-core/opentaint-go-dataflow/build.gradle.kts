import OpentaintIrDependency.opentaint_ir_api_go
import OpentaintIrDependency.opentaint_ir_api_storage
import OpentaintIrDependency.opentaint_ir_core_go
import OpentaintIrDependency.opentaint_ir_storage
import OpentaintUtilDependency.opentaintUtilCommon
import org.opentaint.common.KotlinDependency
import org.opentaint.common.resolveIncludedProjectTask

plugins {
    id("kotlin-conventions")
    kotlinSerialization()
}

dependencies {
    api(project(":opentaint-dataflow"))
    implementation(opentaintUtilCommon)

    implementation("org.opentaint.opentaint-configuration-rules:configuration-rules-jvm")
    implementation("org.opentaint.opentaint-configuration-rules:configuration-rules-go")
    implementation("org.opentaint.config:go-config")

    implementation(opentaint_ir_api_go)
    implementation(opentaint_ir_core_go)
    implementation(opentaint_ir_api_storage)
    implementation(opentaint_ir_storage)

    implementation(KotlinDependency.Libs.kotlin_logging)
    implementation(KotlinDependency.Libs.reflect)
    implementation(KotlinDependency.Libs.kaml)

    implementation(Libs.fastutil)

    implementation(Libs.sarif4k)
}

tasks.withType<Test> {
    ensureGoEnvInitialized()

    doFirst {
        environment(goEnvironment())
    }

    systemProperty("GO_ALIAS_SAMPLES_DIR", layout.projectDirectory.dir("samples-go-alias").asFile.absolutePath)
}

val opentaintGoEnvKey = "opentaint.go.env"

fun goEnvironment(): Map<String, Any> {
    val goEnv = mutableMapOf<String, Any>()
    setupOpentaintGoEnvironment(goEnv)
    return goEnv
}

@Suppress("UNCHECKED_CAST")
fun setupOpentaintGoEnvironment(goEnv: MutableMap<String, Any>) {
    val initializer = findOpentaintGoEnvInitializer() ?: return
    val env = initializer.extra.get(opentaintGoEnvKey) as Map<String, Any>
    goEnv += env
}

fun Task.ensureGoEnvInitialized() {
    val initializer = findOpentaintGoEnvInitializer() ?: return
    dependsOn(initializer)
}

fun findOpentaintGoEnvInitializer(): Task? {
    val irProject = gradle.parent?.includedBuilds?.find { it.name == "opentaint-ir" } ?: return null
    return irProject.resolveIncludedProjectTask(":go:setupGoEnvironment")
}
