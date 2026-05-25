plugins {
    `kotlin-conventions`
}

tasks.withType<ProcessResources> {
    val configDir = layout.projectDirectory.dir("config")

    from(configDir)
}
