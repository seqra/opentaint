package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodEntrySink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodSink
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst

class JIRBackwardSinkSelection(private val base: TaintRulesProvider) : TaintRulesProvider by base {
    @Volatile
    var selected: Map<CommonInst, Set<TaintConfigurationSink>>? = null

    override fun sinkRulesForMethod(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        allRelevant: Boolean
    ): Iterable<TaintMethodSink> = base.sinkRulesForMethod(method, statement, fact, allRelevant).selectedAt(statement)

    override fun sinkRulesForMethodEntry(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        allRelevant: Boolean
    ): Iterable<TaintMethodEntrySink> =
        base.sinkRulesForMethodEntry(method, statement, fact, allRelevant).selectedAt(statement)

    override fun sinkRulesForMethodExit(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        initialFacts: Set<InitialFactAp>?,
        allRelevant: Boolean
    ): Iterable<TaintMethodExitSink> =
        base.sinkRulesForMethodExit(method, statement, fact, initialFacts, allRelevant).selectedAt(statement)

    private fun <T : TaintConfigurationSink> Iterable<T>.selectedAt(statement: CommonInst): Iterable<T> {
        val selection = selected ?: return this
        val rules = selection[statement] ?: return emptyList()
        return filter { it in rules }
    }
}
