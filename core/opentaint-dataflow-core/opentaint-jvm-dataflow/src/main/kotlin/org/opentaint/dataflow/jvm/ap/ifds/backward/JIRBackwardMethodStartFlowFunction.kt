package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodStartFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodStartFlowFunction.StartFact
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodStartFlowFunction

class JIRBackwardMethodStartFlowFunction(
    apManager: ApManager,
    context: JIRBackwardMethodAnalysisContext,
    private val exceptionalExit: Boolean,
) : MethodStartFlowFunction {
    private val forwardStartFlowFunction = JIRMethodStartFlowFunction(apManager, context)

    override fun propagateZero(): List<StartFact> = listOf(StartFact.Zero)

    override fun propagateFact(fact: FinalFactAp): List<StartFact.Fact> {
        if (exceptionalExit) return emptyList()
        return forwardStartFlowFunction.propagateFact(fact)
    }
}
