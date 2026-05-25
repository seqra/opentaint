package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.go.GoFunctionSignature

class GoTaintRulesProvider(val configuration: GoTaintConfiguration) {
    fun sourceRulesForGlobal(globalName: String): List<TaintRule.GlobalReadSource> =
        configuration.sourceForGlobal(globalName)

    fun sourceRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean = false): List<TaintRule.Source> =
        configuration.sourceForFunction(signature, allRelevant)

    fun sinkRulesForCall(signature: GoFunctionSignature): List<TaintRule.Sink> =
        configuration.sinkForFunction(signature)

    fun passThroughRulesForCall(signature: GoFunctionSignature): List<TaintRule.PassThrough> =
        configuration.passThroughForFunction(signature)

    fun cleanerRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean = false): List<TaintRule.Cleaner> =
        configuration.cleanerForFunction(signature, allRelevant)
}
