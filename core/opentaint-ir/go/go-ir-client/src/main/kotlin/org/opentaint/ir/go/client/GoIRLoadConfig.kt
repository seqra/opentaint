package org.opentaint.ir.go.client

enum class GoIRLoadMode { FULL, PROJECT }

data class GoIRLoadConfig(
    val mode: GoIRLoadMode = GoIRLoadMode.PROJECT,
    val patterns: List<String> = listOf("./..."),
    val projectModules: Set<String> = emptySet(),
    val instantiateGenerics: Boolean = true,
    val sanityCheck: Boolean = true,
)
