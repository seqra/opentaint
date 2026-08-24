package org.opentaint.dataflow.python.adapter

import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRCallArgKind
import org.opentaint.ir.api.python.PIRInstruction

class PIRCallExprAdapter(
    val pirCall: PIRCall,
) : CommonCallExpr {

    override val typeName: String get() = "call"

    override val args: List<CommonValue>
        get() = pirCall.args
            .filter { it.kind == PIRCallArgKind.POSITIONAL || it.kind == PIRCallArgKind.KEYWORD }
            .map { it.value }
}

val PIRInstruction.callExpr: PIRCallExprAdapter?
    get() = if (this is PIRCall) PIRCallExprAdapter(this) else null
