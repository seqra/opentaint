package org.opentaint.ir.go.client

import org.opentaint.ir.go.api.GoIRProgram

/** Model policy and transformer installation, separate from wire deserialization. */
internal object GoIRModelLoader {
    fun apply(build: GoIRDeserializer.DeserializedGoIRBuild): GoIRProgram {
        if (build.models.isEmpty()) return build.program
        val definitions = build.models.map { model ->
            val program = GoIRDeserializer().deserializeProgram(model.program)
            try {
                GoIRModelDefinition.create(model.source, program)
            } catch (error: IllegalArgumentException) {
                throw IllegalArgumentException("invalid Go model ${model.source}: ${error.message}", error)
            }
        }
        build.program.install(listOf(GoIRModelTransformer(build.program, definitions)))
        return build.program
    }
}
