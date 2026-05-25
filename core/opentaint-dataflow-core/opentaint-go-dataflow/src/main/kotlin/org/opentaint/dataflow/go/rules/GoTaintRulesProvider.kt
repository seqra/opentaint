package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.go.GoFunctionSignature

class GoTaintRulesProvider(val configuration: GoTaintConfiguration) {
    fun sourceRulesForGlobal(globalName: String): List<TaintRules.GlobalReadSource> =
        configuration.sourceForGlobal(globalName)

    fun sourceRulesForCall(signature: GoFunctionSignature): List<TaintRules.Source> =
        configuration.sourceForFunction(signature)

    fun sinkRulesForCall(signature: GoFunctionSignature): List<TaintRules.Sink> =
        configuration.sinkForFunction(signature)

    fun passThroughRulesForCall(signature: GoFunctionSignature): List<TaintRules.PassThrough> =
        configuration.passThroughForFunction(signature)

    fun cleanerRulesForCall(signature: GoFunctionSignature): List<TaintRules.Cleaner> =
        configuration.cleanerForFunction(signature)
}
