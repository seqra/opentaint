import OpentaintConfigurationDependency.opentaintRulesGo
import org.opentaint.common.KotlinDependency

plugins {
    `kotlin-conventions`
}

dependencies {
    implementation(opentaintRulesGo)

    implementation(KotlinDependency.Libs.kotlinx_serialization_core)
    implementation(KotlinDependency.Libs.kaml)
}

tasks.withType<ProcessResources> {
    val configDir = layout.projectDirectory.dir("config")

    from(configDir)
}
