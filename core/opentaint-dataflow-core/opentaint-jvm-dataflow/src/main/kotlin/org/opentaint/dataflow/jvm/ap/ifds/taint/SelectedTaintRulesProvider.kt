package org.opentaint.dataflow.jvm.ap.ifds.taint

import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.Action
import org.opentaint.dataflow.configuration.jvm.TaintCleaner
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodEntrySink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.TaintPassThrough
import org.opentaint.dataflow.configuration.jvm.TaintStaticFieldSource
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.JIRField
import org.opentaint.ir.api.jvm.cfg.JIRInst

class SelectedTaintRulesProvider(
    private val delegate: TaintRulesProvider,
) : TaintRulesProvider {
    private class SelectedRule<T : TaintConfigurationItem> {
        private val perStatement = hashMapOf<JIRInst, MutableList<T>>()
        fun find(statement: JIRInst): List<T> = perStatement[statement] ?: emptyList()
        fun add(statement: JIRInst, rule: T) {
            perStatement.getOrPut(statement) { mutableListOf() }.add(rule)
        }
    }

    private class SelectedRuleSet {
        val methodSource = SelectedRule<TaintMethodSource>()
        val methodEntrySource = SelectedRule<TaintEntryPointSource>()
        val methodExitSource = SelectedRule<TaintMethodExitSource>()
        val staticFieldSource = SelectedRule<TaintStaticFieldSource>()

        val methodSink = SelectedRule<TaintMethodSink>()
        val methodEntrySink = SelectedRule<TaintMethodEntrySink>()
        val methodExitSink = SelectedRule<TaintMethodExitSink>()

        val methodCleaner = SelectedRule<TaintCleaner>()

    }

    @Volatile
    private var selected: SelectedRuleSet? = null

    fun select(rules: Map<CommonInst, Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>>?) {
        if (rules == null) {
            selected = null
            return
        }

        val selected = SelectedRuleSet()

        for ((inst, instRules) in rules.entries) {
            if (inst !is JIRInst) continue
            for ((rule, actions) in instRules) {
                if (rule !is TaintConfigurationItem) continue

                when (rule) {
                    is TaintMethodSource -> {
                        val actions = rule.actionsAfter.relevantActions(actions) ?: continue
                        val selectedRule = rule.copy(actionsAfter = actions)
                        selected.methodSource.add(inst, selectedRule)
                    }

                    is TaintCleaner -> {
                        val actions = rule.actionsAfter.relevantActions(actions) ?: continue
                        val selectedRule = rule.copy(actionsAfter = actions)
                        selected.methodCleaner.add(inst, selectedRule)
                    }

                    is TaintMethodEntrySink -> {
                        check(actions.isEmpty()) { "Sink rule has selected actions: $rule" }
                        selected.methodEntrySink.add(inst, rule)
                    }

                    is TaintMethodExitSink -> {
                        check(actions.isEmpty()) { "Sink rule has selected actions: $rule" }
                        selected.methodExitSink.add(inst, rule)
                    }

                    is TaintMethodSink -> {
                        check(actions.isEmpty()) { "Sink rule has selected actions: $rule" }
                        selected.methodSink.add(inst, rule)
                    }

                    is TaintEntryPointSource -> {
                        val actions = rule.actionsAfter.relevantActions(actions) ?: continue
                        val selectedRule = rule.copy(actionsAfter = actions)
                        selected.methodEntrySource.add(inst, selectedRule)
                    }

                    is TaintMethodExitSource -> {
                        val actions = rule.actionsAfter.relevantActions(actions) ?: continue
                        val selectedRule = rule.copy(actionsAfter = actions)
                        selected.methodExitSource.add(inst, selectedRule)
                    }

                    is TaintStaticFieldSource -> {
                        val actions = rule.actionsAfter.relevantActions(actions) ?: continue
                        val selectedRule = rule.copy(actionsAfter = actions)
                        selected.staticFieldSource.add(inst, selectedRule)
                    }

                    is TaintPassThrough -> continue
                }
            }
        }

        this.selected = selected
    }

    override fun selectRules(ruleIds: Set<String>) {
        delegate.selectRules(ruleIds)
    }

    override fun entryPointRulesForMethod(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        allRelevant: Boolean,
    ): Iterable<TaintEntryPointSource> {
        val s = selected
        if (s == null || allRelevant) {
            return delegate.entryPointRulesForMethod(method, statement, fact, allRelevant)
        }

        return s.methodEntrySource.find(statement as JIRInst)
    }

    override fun sinkRulesForMethodEntry(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        allRelevant: Boolean,
    ): Iterable<TaintMethodEntrySink> {
        val s = selected
        if (s == null || allRelevant) {
            return delegate.sinkRulesForMethodEntry(method, statement, fact, allRelevant)
        }

        return s.methodEntrySink.find(statement as JIRInst)
    }

    override fun sourceRulesForMethod(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        allRelevant: Boolean,
    ): Iterable<TaintMethodSource> {
        val s = selected
        if (s == null || allRelevant) {
            return delegate.sourceRulesForMethod(method, statement, fact, allRelevant)
        }

        return s.methodSource.find(statement as JIRInst)
    }

    override fun exitSourceRulesForMethod(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        allRelevant: Boolean,
    ): Iterable<TaintMethodExitSource> {
        val s = selected
        if (s == null || allRelevant) {
            return delegate.exitSourceRulesForMethod(method, statement, fact, allRelevant)
        }

        return s.methodExitSource.find(statement as JIRInst)
    }

    override fun sourceRulesForStaticField(
        field: JIRField,
        statement: CommonInst,
        fact: FactAp?,
        allRelevant: Boolean,
    ): Iterable<TaintStaticFieldSource> {
        val s = selected
        if (s == null || allRelevant) {
            return delegate.sourceRulesForStaticField(field, statement, fact, allRelevant)
        }

        return s.staticFieldSource.find(statement as JIRInst)
    }

    override fun sinkRulesForMethod(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        allRelevant: Boolean,
    ): Iterable<TaintMethodSink> {
        val s = selected
        if (s == null || allRelevant) {
            return delegate.sinkRulesForMethod(method, statement, fact, allRelevant)
        }

        return s.methodSink.find(statement as JIRInst)
    }

    override fun sinkRulesForMethodExit(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        initialFacts: Set<InitialFactAp>?,
        allRelevant: Boolean,
    ): Iterable<TaintMethodExitSink> {
        val s = selected
        if (s == null || allRelevant) {
            return delegate.sinkRulesForMethodExit(method, statement, fact, initialFacts, allRelevant)
        }

        return s.methodExitSink.find(statement as JIRInst)
    }

    override fun cleanerRulesForMethod(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        allRelevant: Boolean,
    ): Iterable<TaintCleaner> = delegate.cleanerRulesForMethod(method, statement, fact, allRelevant)

    override fun passTroughRulesForMethod(
        method: CommonMethod,
        statement: CommonInst?,
        fact: FactAp?,
        allRelevant: Boolean,
    ): Iterable<TaintPassThrough> =
        delegate.passTroughRulesForMethod(method, statement, fact, allRelevant)

    private fun <T : Action> List<T>.relevantActions(relevant: Set<CommonTaintAction>): List<T>? =
        filter { it in relevant }.takeIf { it.isNotEmpty() }
}
