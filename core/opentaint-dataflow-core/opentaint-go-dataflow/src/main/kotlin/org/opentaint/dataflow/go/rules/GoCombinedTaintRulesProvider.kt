package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.go.GoFieldSignature
import org.opentaint.dataflow.go.GoFunctionSignature
import org.opentaint.dataflow.go.GoGlobalFieldSignature
import org.opentaint.ir.go.inst.GoIRInst

class GoCombinedTaintRulesProvider(
    private val base: GoTaintRulesProvider,
    private val combined: GoTaintRulesProvider,
    private val options: CombinationOptions = CombinationOptions(),
) : GoTaintRulesProvider {
    enum class CombinationMode { EXTEND, OVERRIDE, IGNORE }

    data class CombinationOptions(
        val source: CombinationMode = CombinationMode.OVERRIDE,
        val sink: CombinationMode = CombinationMode.OVERRIDE,
        val passThrough: CombinationMode = CombinationMode.EXTEND,
        val cleaner: CombinationMode = CombinationMode.EXTEND,
        val globalSource: CombinationMode = CombinationMode.OVERRIDE,
    )

    override fun sourceRulesForGlobal(signature: GoGlobalFieldSignature, statement: GoIRInst) =
        combine(options.globalSource,
            base.sourceRulesForGlobal(signature, statement),
            combined.sourceRulesForGlobal(signature, statement)
        )

    override fun sourceRulesForFieldRead(signature: GoFieldSignature, statement: GoIRInst) =
        combine(
            options.source,
            base.sourceRulesForFieldRead(signature, statement),
            combined.sourceRulesForFieldRead(signature, statement)
        )

    override fun sourceRulesForCall(signature: GoFunctionSignature, statement: GoIRInst, allRelevant: Boolean) =
        combine(options.source,
            base.sourceRulesForCall(signature, statement, allRelevant),
            combined.sourceRulesForCall(signature, statement, allRelevant))

    override fun sinkRulesForCall(signature: GoFunctionSignature, statement: GoIRInst) =
        combine(options.sink,
            base.sinkRulesForCall(signature, statement),
            combined.sinkRulesForCall(signature, statement))

    override fun passThroughRulesForCall(signature: GoFunctionSignature, statement: GoIRInst) =
        combine(options.passThrough,
            base.passThroughRulesForCall(signature, statement),
            combined.passThroughRulesForCall(signature, statement))

    override fun cleanerRulesForCall(signature: GoFunctionSignature, statement: GoIRInst, allRelevant: Boolean) =
        combine(options.cleaner,
            base.cleanerRulesForCall(signature, statement, allRelevant),
            combined.cleanerRulesForCall(signature, statement, allRelevant))

    override fun selectRules(ruleIds: Set<String>) {
        base.selectRules(ruleIds)
        combined.selectRules(ruleIds)
    }

    private fun <T> combine(mode: CombinationMode, base: List<T>, extra: List<T>): List<T> = when (mode) {
        CombinationMode.EXTEND -> base + extra
        CombinationMode.OVERRIDE -> extra.takeIf { it.isNotEmpty() } ?: base
        CombinationMode.IGNORE -> base
    }
}
