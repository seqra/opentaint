package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler
import org.opentaint.ir.api.python.PIRCall

class PIRMethodCallSummaryHandler(
    private val callInst: PIRCall,
    private val ctx: PIRMethodAnalysisContext,
    private val callResolver: PIRCallResolver, // TODO make call resolver free
    override val factTypeChecker: FactTypeChecker,
) : MethodCallSummaryHandler {

    private val factMapper get() = ctx.methodCallFactMapper as PIRMethodCallFactMapper

    /**
     * Translates a callee-frame exit fact into the caller's frame.
     *
     * The fact mapper produces offset-free output (callee `Argument(i)`
     * mapped positionally to `call.args[i]`). This handler applies
     * [PIRMethodCallFactMapper.offsetExit] to re-introduce the
     * `self`/`cls` offset before delivering the caller-frame fact.
     */
    override fun mapMethodExitToReturnFlowFact(fact: FinalFactAp): List<FinalFactAp> {
        val callee = callResolver.resolve(callInst).firstOrNull() ?: return emptyList()
        return factMapper
            .mapMethodExitToReturnFlowFact(callInst, fact, factTypeChecker)
            .mapNotNull { exitFact ->
                val newBase = factMapper.offsetExit(callInst, callee, exitFact.base) ?: return@mapNotNull null
                exitFact.rebase(newBase)
            }
    }
}
