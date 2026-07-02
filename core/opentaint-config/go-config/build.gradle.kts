import OpentaintConfigurationDependency.opentaintRulesGo
import org.opentaint.common.KotlinDependency

plugins {
    `kotlin-conventions`
}

dependencies {
    api(project(":java-config"))
    implementation(opentaintRulesGo)

    implementation(KotlinDependency.Libs.kotlinx_serialization_core)
    implementation(KotlinDependency.Libs.kaml)
}

tasks.withType<ProcessResources> {
    val modelDir = layout.projectDirectory.dir("../../../model/go")

    from(modelDir) {
        into("model/go")
    }
}
