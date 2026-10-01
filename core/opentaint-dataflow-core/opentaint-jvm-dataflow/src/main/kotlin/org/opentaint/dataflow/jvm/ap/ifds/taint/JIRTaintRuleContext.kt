package org.opentaint.dataflow.jvm.ap.ifds.taint

import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
import org.opentaint.dataflow.configuration.jvm.TaintCleaner
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodEntrySink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.TaintPassThrough
import org.opentaint.dataflow.configuration.jvm.TaintStaticFieldSource
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.ir.api.jvm.JIRField
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst

interface JIRTaintRuleContext : TaintAnalysisContext {
    val externalMethodTracker: ExternalMethodTracker?

    fun bindAnalysisContext(analysisContext: JIRMethodAnalysisContext)

    fun reset()

    fun allRelevantSourceRulesForCallStatement(statement: JIRInst): Iterable<TaintMethodSource>

    fun allRelevantCleanRulesForCallStatement(statement: JIRInst): Iterable<TaintCleaner>

    fun sourceRulesForCallStatement(
        statement: JIRInst,
        callExpr: JIRCallExpr,
        returnValue: JIRImmediate?,
        fact: FinalFactAp?
    ): List<RuleWithCondition<TaintMethodSource>>

    fun sinkRulesForCallStatement(
        statement: JIRInst,
        callExpr: JIRCallExpr,
        returnValue: JIRImmediate?,
        fact: FinalFactAp?
    ): List<RuleWithCondition<TaintMethodSink>>

    fun cleanRulesForCallStatement(
        statement: JIRInst,
        callExpr: JIRCallExpr,
        returnValue: JIRImmediate?,
        fact: FinalFactAp?
    ): List<RuleWithCondition<TaintCleaner>>

    fun passRulesForCallStatement(
        statement: JIRInst,
        callExpr: JIRCallExpr,
        returnValue: JIRImmediate?,
        fact: FinalFactAp?
    ): List<RuleWithCondition<TaintPassThrough>>

    fun sourceRulesForStaticField(
        field: JIRField,
        statement: JIRInst,
        fact: FinalFactAp?
    ): List<RuleWithCondition<TaintStaticFieldSource>>

    fun sourceRulesForMethodExit(
        statement: JIRInst,
        fact: FinalFactAp?
    ): List<RuleWithCondition<TaintMethodExitSource>>

    fun sinkRulesForMethodExit(
        statement: JIRInst,
        fact: FinalFactAp?,
        initialFacts: Set<InitialFactAp>?
    ): List<RuleWithCondition<TaintMethodExitSink>>

    fun sinkRulesForMethodEntry(
        statement: JIRInst,
        fact: FinalFactAp?
    ): List<RuleWithCondition<TaintMethodEntrySink>>

    fun sourceRulesForMethodEntry(
        statement: JIRInst,
        fact: FinalFactAp?
    ): List<RuleWithCondition<TaintEntryPointSource>>
}
