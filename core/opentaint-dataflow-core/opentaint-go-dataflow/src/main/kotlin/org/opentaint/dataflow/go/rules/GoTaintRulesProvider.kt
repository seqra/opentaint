package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.go.GoFieldSignature
import org.opentaint.dataflow.go.GoFunctionSignature
import org.opentaint.dataflow.go.GoGlobalFieldSignature
import org.opentaint.ir.go.inst.GoIRInst

interface GoTaintRulesProvider {
    fun sourceRulesForGlobal(signature: GoGlobalFieldSignature, statement: GoIRInst): List<TaintRule.GlobalReadSource>
    fun sourceRulesForFieldRead(signature: GoFieldSignature, statement: GoIRInst): List<TaintRule.FieldReadSource>
    fun sourceRulesForCall(signature: GoFunctionSignature, statement: GoIRInst, allRelevant: Boolean = false): List<TaintRule.Source>
    fun sinkRulesForCall(signature: GoFunctionSignature, statement: GoIRInst): List<TaintRule.Sink>
    fun passThroughRulesForCall(signature: GoFunctionSignature, statement: GoIRInst): List<TaintRule.PassThrough>
    fun cleanerRulesForCall(signature: GoFunctionSignature, statement: GoIRInst, allRelevant: Boolean = false): List<TaintRule.Cleaner>
    fun selectRules(ruleIds: Set<String>) = Unit
}
