package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.go.GoFunctionSignature

interface GoTaintRulesProvider {
    fun sourceRulesForGlobal(globalName: String, fieldType: String): List<TaintRule.GlobalReadSource>
    fun sourceRulesForFieldRead(fieldName: String, fieldType: String): List<TaintRule.FieldReadSource>
    fun sourceRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean = false): List<TaintRule.Source>
    fun sinkRulesForCall(signature: GoFunctionSignature): List<TaintRule.Sink>
    fun passThroughRulesForCall(signature: GoFunctionSignature): List<TaintRule.PassThrough>
    fun cleanerRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean = false): List<TaintRule.Cleaner>
}
