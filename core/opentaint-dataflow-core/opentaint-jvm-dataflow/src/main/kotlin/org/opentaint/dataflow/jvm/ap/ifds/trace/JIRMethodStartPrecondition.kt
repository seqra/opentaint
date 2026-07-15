package org.opentaint.dataflow.jvm.ap.ifds.trace

import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.MethodStartPrecondition
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSource
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.dataflow.taint.InitialFactReader
import org.opentaint.dataflow.taint.TaintSourceActionPreconditionEvaluator
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.util.onSome

class JIRMethodStartPrecondition(
    private val apManager: ApManager,
    private val context: JIRMethodAnalysisContext,
) : MethodStartPrecondition {
    override fun factPrecondition(fact: InitialFactAp): List<TaintRulePrecondition.Source> {
        val entryFactReader = InitialFactReader(fact, apManager)
        val sourcePreconditionEvaluator = TaintSourceActionPreconditionEvaluator(entryFactReader)
        val rules = context.taint.sourceRulesForMethodEntry(context.methodEntryPoint.statement as JIRInst, fact = null)
        val result = TaintConfigUtils.applyEntryPointConfig(rules, sourcePreconditionEvaluator)

        result.onSome { sourceActions ->
            return sourceActions.map {
                TaintRulePrecondition.Source(
                    it.first as CommonTaintConfigurationSource,
                    setOf(it.second)
                )
            }
        }

        return emptyList()
    }
}
