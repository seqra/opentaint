package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.go.GoFunctionSignature

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

    override fun sourceRulesForGlobal(globalName: String, fieldType: String) =
        combine(options.globalSource,
            base.sourceRulesForGlobal(globalName, fieldType),
            combined.sourceRulesForGlobal(globalName, fieldType)
        )

    override fun sourceRulesForFieldRead(fieldName: String, fieldType: String) =
        combine(
            options.source,
            base.sourceRulesForFieldRead(fieldName, fieldType),
            combined.sourceRulesForFieldRead(fieldName, fieldType)
        )

    override fun sourceRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean) =
        combine(options.source,
            base.sourceRulesForCall(signature, allRelevant),
            combined.sourceRulesForCall(signature, allRelevant))

    override fun sinkRulesForCall(signature: GoFunctionSignature) =
        combine(options.sink,
            base.sinkRulesForCall(signature),
            combined.sinkRulesForCall(signature))

    override fun passThroughRulesForCall(signature: GoFunctionSignature) =
        combine(options.passThrough,
            base.passThroughRulesForCall(signature),
            combined.passThroughRulesForCall(signature))

    override fun cleanerRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean) =
        combine(options.cleaner,
            base.cleanerRulesForCall(signature, allRelevant),
            combined.cleanerRulesForCall(signature, allRelevant))

    private fun <T> combine(mode: CombinationMode, base: List<T>, extra: List<T>): List<T> = when (mode) {
        CombinationMode.EXTEND -> base + extra
        CombinationMode.OVERRIDE -> extra.takeIf { it.isNotEmpty() } ?: base
        CombinationMode.IGNORE -> base
    }
}
