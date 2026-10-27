package org.opentaint.ir.go.client

import org.opentaint.ir.go.api.GoIRProgram

/** Model policy and transformer installation, separate from wire deserialization. */
internal object GoIRModelLoader {
    fun apply(build: GoIRDeserializer.DeserializedGoIRBuild): GoIRProgram {
        if (build.models.isEmpty()) return build.program
        val definitions = build.models.map { model ->
            val rawProgram = GoIRDeserializer().deserializeProgram(model.program)
            val paths = try {
                GoIRModelPathTransformer.create(rawProgram)
            } catch (error: IllegalArgumentException) {
                throw IllegalArgumentException("invalid Go model ${model.source}: ${error.message}", error)
            }
            GoIRModelDefinition(model.source, GoIRTransformerChain(rawProgram, listOf(paths)), paths.targets)
        }
        return GoIRTransformerChain(build.program, listOf(GoIRModelTransformer(build.program, definitions)))
    }
}
