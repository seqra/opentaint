import OpentaintIrDependency.opentaint_ir_api_python
import org.opentaint.common.JunitDependencies
import org.opentaint.common.KotlinDependency

plugins {
    id("kotlin-conventions")
    kotlinSerialization()
}

dependencies {
    api(project(":configuration-rules-common"))

    implementation(opentaint_ir_api_python)
    implementation(KotlinDependency.Libs.kotlinx_serialization_core)
    implementation(KotlinDependency.Libs.kaml)

    testImplementation(platform(JunitDependencies.Libs.junit_bom))
    testImplementation(JunitDependencies.Libs.junit_jupiter)
}

val pythonConfigFile = rootProject.layout.projectDirectory
    .dir("../opentaint-dataflow-core/opentaint-python-dataflow/config/config")
    .file("config.yaml")
    .asFile

tasks.test {
    systemProperty("python.config.path", pythonConfigFile.absolutePath)
    inputs.file(pythonConfigFile)
}