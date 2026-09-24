package org.opentaint.jvm.sast.dataflow.backward

import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationItem
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.JIRField

class RuleIdSelectingProvider(private val delegate: TaintRulesProvider) : TaintRulesProvider {
    @Volatile
    private var selected: Set<String>? = null

    override fun selectRules(ruleIds: Set<String>) {
        selected = ruleIds.toSet()
        delegate.selectRules(ruleIds)
    }

    private fun <T : TaintConfigurationItem> Iterable<T>.select(allRelevant: Boolean): Iterable<T> {
        val ids = selected
        if (allRelevant || ids == null) return this
        return filter { rule -> rule.serializedId.let { it == null || it in ids } }
    }

    override fun entryPointRulesForMethod(method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean) =
        delegate.entryPointRulesForMethod(method, statement, fact, allRelevant).select(allRelevant)

    override fun sourceRulesForMethod(method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean) =
        delegate.sourceRulesForMethod(method, statement, fact, allRelevant).select(allRelevant)

    override fun exitSourceRulesForMethod(method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean) =
        delegate.exitSourceRulesForMethod(method, statement, fact, allRelevant).select(allRelevant)

    override fun sinkRulesForMethod(method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean) =
        delegate.sinkRulesForMethod(method, statement, fact, allRelevant).select(allRelevant)

    override fun sinkRulesForMethodEntry(method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean) =
        delegate.sinkRulesForMethodEntry(method, statement, fact, allRelevant).select(allRelevant)

    override fun sinkRulesForMethodExit(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        initialFacts: Set<InitialFactAp>?,
        allRelevant: Boolean,
    ) = delegate.sinkRulesForMethodExit(method, statement, fact, initialFacts, allRelevant).select(allRelevant)

    override fun passTroughRulesForMethod(method: CommonMethod, statement: CommonInst?, fact: FactAp?, allRelevant: Boolean) =
        delegate.passTroughRulesForMethod(method, statement, fact, allRelevant).select(allRelevant)

    override fun cleanerRulesForMethod(method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean) =
        delegate.cleanerRulesForMethod(method, statement, fact, allRelevant).select(allRelevant)

    override fun sourceRulesForStaticField(field: JIRField, statement: CommonInst, fact: FactAp?, allRelevant: Boolean) =
        delegate.sourceRulesForStaticField(field, statement, fact, allRelevant).select(allRelevant)
}
