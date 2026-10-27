package org.opentaint.ir.go.client

import org.opentaint.ir.go.api.*

/** Maps model-addressed packages (`opentaint/<target>`) and their symbols onto their target paths. */
internal class GoIRModelPathTransformer private constructor(
    private val replacements: Map<String, String>,
) : GoIRTransformer {
    val targets: Set<String> = replacements.values.toSet()
    private val orderedModelPaths = replacements.keys.sortedByDescending(String::length)

    override fun packagePath(importPath: String): String = replacements[importPath] ?: importPath

    override fun symbolName(fullName: String): String = orderedModelPaths.fold(fullName) { result, modelPath ->
        result.replace(modelPath, replacements.getValue(modelPath))
    }

    companion object {
        fun create(program: GoIRProgram): GoIRModelPathTransformer {
            val replacements = program.packages.values
                .filterNot { it.isDependency || it.isStdlib || it.importPath == UNIVERSE_PACKAGE_PATH }
                .associate { pkg ->
                    require(pkg.importPath.startsWith(GO_MODEL_PREFIX)) {
                        "Go model package \"${pkg.importPath}\" is not model-addressed, " +
                            "its import path must be ${GO_MODEL_PREFIX}<target-import-path>"
                    }
                    val target = pkg.importPath.removePrefix(GO_MODEL_PREFIX)
                    require(target.isNotEmpty()) {
                        "Go model package \"${pkg.importPath}\" has an empty target package"
                    }
                    pkg.importPath to target
                }
            require(replacements.isNotEmpty()) {
                "Go model contains no model-addressed packages, expected at least one package " +
                    "under $GO_MODEL_PREFIX"
            }
            return GoIRModelPathTransformer(replacements)
        }
    }
}

private const val GO_MODEL_PREFIX = "opentaint/"
private const val UNIVERSE_PACKAGE_PATH = "<universe>"
