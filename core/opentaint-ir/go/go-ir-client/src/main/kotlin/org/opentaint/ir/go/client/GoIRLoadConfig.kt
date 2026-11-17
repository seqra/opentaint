package org.opentaint.ir.go.client

import java.nio.file.Path

enum class GoIRLoadMode { FULL, PROJECT }

data class GoIRLoadConfig(
    val mode: GoIRLoadMode = GoIRLoadMode.PROJECT,
    val patterns: List<String> = listOf("./..."),
    val projectModules: Set<String> = emptySet(),
    val instantiateGenerics: Boolean = true,
    val sanityCheck: Boolean = true,
    val modelDirs: List<Path> = emptyList(),
    // GOROOT for the `go` commands of the build; `go` uses its own when null.
    val goRoot: Path? = null,
)
