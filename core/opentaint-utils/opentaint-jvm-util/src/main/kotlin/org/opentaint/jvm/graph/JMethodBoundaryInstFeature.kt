package org.opentaint.jvm.graph

import org.opentaint.ir.api.jvm.JIRInstExtFeature
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRInstList
import org.opentaint.ir.impl.cfg.JIRInstListImpl
import org.opentaint.ir.impl.cfg.JIRInstLocationImpl

object JMethodBoundaryInstFeature : JIRInstExtFeature {

    override fun transformInstList(method: JIRMethod, list: JIRInstList<JIRInst>): JIRInstList<JIRInst> {
        if (list.size == 0) return list
        if (list.instructions.any { it is JMethodBoundaryInst }) return list

        val instructions = list.instructions.toMutableList()
        instructions += JMethodEnterInst(boundaryLocation(method, instructions.size))
        instructions += JMethodExitNormalInst(boundaryLocation(method, instructions.size))
        instructions += JMethodExitExceptionalInst(boundaryLocation(method, instructions.size))

        return JIRInstListImpl(instructions)
    }

    private const val BOUNDARY_LINE_NUMBER = -1

    private fun boundaryLocation(method: JIRMethod, index: Int) =
        JIRInstLocationImpl(method, index, BOUNDARY_LINE_NUMBER)
}
