import OpentaintConfigurationDependency.opentaintRulesJvm

plugins {
    `kotlin-conventions`
}

dependencies {
    implementation(opentaintRulesJvm)
}

tasks.withType<ProcessResources> {
    val modelDir = layout.projectDirectory.dir("../../../model/java")

    from(modelDir) {
        include("config/**")
        into("model/java")
    }
}
