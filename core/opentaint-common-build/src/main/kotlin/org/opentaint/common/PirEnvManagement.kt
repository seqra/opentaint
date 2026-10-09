package org.opentaint.common

import org.gradle.api.Project
import org.gradle.api.Task
import org.gradle.kotlin.dsl.extra

val pirEnvironmentExtraKey = "opentaint.pir.env"

fun Project.pirEnvironment(): Map<String, Any> {
    val pirEnv = mutableMapOf<String, Any>()
    setupOpentaintPirEnvironment(pirEnv)
    return pirEnv
}

@Suppress("UNCHECKED_CAST")
fun Project.setupOpentaintPirEnvironment(pirEnv: MutableMap<String, Any>) {
    val initializer = findOpentaintPirEnvInitializer() ?: return
    val env = initializer.extra.get(pirEnvironmentExtraKey) as Map<String, Any>
    pirEnv += env
}

fun Task.ensurePirEnvInitialized() {
    val initializer = project.findOpentaintPirEnvInitializer() ?: return
    dependsOn(initializer)
}

fun Project.findOpentaintPirEnvInitializer(): Task? {
    val irProject = gradle.findIrProject() ?: return null
    return irProject.resolveIncludedProjectTask(":python:setupPirEnvironment")
}
