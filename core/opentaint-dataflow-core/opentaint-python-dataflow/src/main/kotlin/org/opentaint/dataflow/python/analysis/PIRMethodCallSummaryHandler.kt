package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler
import org.opentaint.dataflow.python.PIRCallResolver
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
     * Mirror of the enter pipeline (mapper produces offset-free output,
     * then [PIRMethodCallResolver] applies [PIRMethodCallFactMapper.offsetEnter]):
     * [PIRMethodCallFactMapper.offsetExit] first maps the real callee frame back
     * to the offset-free frame (`Argument(0)` → `This`, `Argument(i)` →
     * `Argument(i - offset)`), then the offset-blind mapper rebases onto the
     * caller's call-site values.
     */
    override fun mapMethodExitToReturnFlowFact(fact: FinalFactAp): List<FinalFactAp> {
        val callee = callResolver.resolveCall(callInst).firstOrNull() ?: return emptyList()
        val offsetFreeBase = factMapper.offsetExit(callInst, callee, fact.base) ?: return emptyList()
        return factMapper.mapMethodExitToReturnFlowFact(callInst, fact.rebase(offsetFreeBase), factTypeChecker)
    }
}
