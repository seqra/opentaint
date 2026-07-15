package org.opentaint.dataflow.ap.ifds.taint

import org.opentaint.dataflow.taint.RuleConditionRewriter

interface TaintAnalysisContext {
    val taintSinkTracker: TaintSinkTracker

    data class RuleWithCondition<R>(
        val rule: R,
        val condition: RuleConditionRewriter.ExprOrConstant,
    )
}

class CommonTaintAnalysisContext(
    override val taintSinkTracker: TaintSinkTracker
) : TaintAnalysisContext

