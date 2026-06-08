package org.opentaint.common

import org.gradle.api.Project
import org.gradle.api.Task
import org.gradle.api.initialization.IncludedBuild
import org.gradle.api.invocation.Gradle
import org.gradle.kotlin.dsl.extra

val goEnvironmentExtraKey = "opentaint.go.env"

fun Project.goEnvironment(): Map<String, Any> {
    val goEnv = mutableMapOf<String, Any>()
    setupOpentaintGoEnvironment(goEnv)
    return goEnv
}

@Suppress("UNCHECKED_CAST")
fun Project.setupOpentaintGoEnvironment(goEnv: MutableMap<String, Any>) {
    val initializer = findOpentaintGoEnvInitializer() ?: return
    val env = initializer.extra.get(goEnvironmentExtraKey) as Map<String, Any>
    goEnv += env
}

fun Task.ensureGoEnvInitialized() {
    val initializer = project.findOpentaintGoEnvInitializer() ?: return
    dependsOn(initializer)
}

fun Project.findOpentaintGoEnvInitializer(): Task? {
    val irProject = gradle.findIrProject() ?: return null
    return irProject.resolveIncludedProjectTask(":go:setupGoEnvironment")
}

private fun Gradle.findIrProject(): IncludedBuild? {
    val currentInclude = includedBuilds.find { it.name == "opentaint-ir" }
    if (currentInclude != null) return currentInclude
    return parent?.findIrProject()
}
