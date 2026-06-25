package org.opentaint.dataflow.jvm.ap.ifds.alias

import org.opentaint.dataflow.ap.ifds.analysis.alias.AAHeapAccessor
import org.opentaint.ir.api.jvm.JIRMethod

interface ExternalCallModelProvider {
    sealed interface Position {
        data object RetVal : Position
        data object This : Position
        data class Arg(val idx: Int) : Position
    }

    data class ExternalObject(
        val pos: Position,
        val accessors: List<AAHeapAccessor>
    )

    data class ExternalAssign(val from: ExternalObject, val to: ExternalObject)

    fun provideModel(method: JIRMethod): List<ExternalAssign>
}
