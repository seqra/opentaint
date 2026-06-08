import OpentaintConfigurationDependency.opentaintRulesPython

plugins {
    `kotlin-conventions`
}

dependencies {
    implementation(opentaintRulesPython)
}

tasks.withType<ProcessResources> {
    val configDir = layout.projectDirectory.dir("config")

    from(configDir)
}
