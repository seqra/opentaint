package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.go.GoFieldSignature
import org.opentaint.dataflow.go.GoFunctionSignature
import org.opentaint.dataflow.go.GoGlobalFieldSignature

interface GoTaintRulesProvider {
    fun sourceRulesForGlobal(signature: GoGlobalFieldSignature): List<TaintRule.GlobalReadSource>
    fun sourceRulesForFieldRead(signature: GoFieldSignature): List<TaintRule.FieldReadSource>
    fun sourceRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean = false): List<TaintRule.Source>
    fun sinkRulesForCall(signature: GoFunctionSignature): List<TaintRule.Sink>
    fun passThroughRulesForCall(signature: GoFunctionSignature): List<TaintRule.PassThrough>
    fun cleanerRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean = false): List<TaintRule.Cleaner>
}
