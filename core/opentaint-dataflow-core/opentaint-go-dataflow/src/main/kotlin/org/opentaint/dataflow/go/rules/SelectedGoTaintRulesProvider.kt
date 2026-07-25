package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.go.GoFieldSignature
import org.opentaint.dataflow.go.GoFunctionSignature
import org.opentaint.dataflow.go.GoGlobalFieldSignature
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.go.inst.GoIRInst

class SelectedGoTaintRulesProvider(
    private val delegate: GoTaintRulesProvider,
) : GoTaintRulesProvider {
    private class SelectedRule<T : TaintRule> {
        private val perStatement = hashMapOf<GoIRInst, MutableList<T>>()

        fun find(statement: GoIRInst): List<T> = perStatement[statement] ?: emptyList()

        fun add(statement: GoIRInst, rule: T) {
            perStatement.getOrPut(statement) { mutableListOf() }.add(rule)
        }
    }

    private class SelectedRuleSet {
        val globalSource = SelectedRule<TaintRule.GlobalReadSource>()
        val fieldSource = SelectedRule<TaintRule.FieldReadSource>()
        val callSource = SelectedRule<TaintRule.Source>()
        val callSink = SelectedRule<TaintRule.Sink>()
        val callCleaner = SelectedRule<TaintRule.Cleaner>()
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
            if (inst !is GoIRInst) continue
            for ((rule, actions) in instRules) {
                if (rule !is TaintRule) continue

                when (rule) {
                    is TaintRule.GlobalReadSource -> {
                        val actions = rule.actionsAfter.relevantActions(actions) ?: continue
                        selected.globalSource.add(inst, rule.copy(actionsAfter = actions))
                    }

                    is TaintRule.FieldReadSource -> {
                        val actions = rule.actionsAfter.relevantActions(actions) ?: continue
                        selected.fieldSource.add(inst, rule.copy(actionsAfter = actions))
                    }

                    is TaintRule.Source -> {
                        val actions = rule.actionsAfter.relevantActions(actions) ?: continue
                        selected.callSource.add(inst, rule.copy(actionsAfter = actions))
                    }

                    is TaintRule.Sink -> {
                        check(actions.isEmpty()) { "Sink rule has selected actions: $rule" }
                        selected.callSink.add(inst, rule)
                    }

                    is TaintRule.Cleaner -> {
                        val actions = rule.actionsAfter.relevantActions(actions) ?: continue
                        selected.callCleaner.add(inst, rule.copy(actionsAfter = actions))
                    }

                    is TaintRule.PassThrough -> continue
                }
            }
        }

        this.selected = selected
    }

    override fun selectRules(ruleIds: Set<String>) {
        delegate.selectRules(ruleIds)
    }

    override fun sourceRulesForGlobal(
        signature: GoGlobalFieldSignature,
        statement: GoIRInst,
    ): List<TaintRule.GlobalReadSource> {
        val s = selected ?: return delegate.sourceRulesForGlobal(signature, statement)
        return s.globalSource.find(statement)
    }

    override fun sourceRulesForFieldRead(
        signature: GoFieldSignature,
        statement: GoIRInst,
    ): List<TaintRule.FieldReadSource> {
        val s = selected ?: return delegate.sourceRulesForFieldRead(signature, statement)
        return s.fieldSource.find(statement)
    }

    override fun sourceRulesForCall(
        signature: GoFunctionSignature,
        statement: GoIRInst,
        allRelevant: Boolean,
    ): List<TaintRule.Source> {
        val s = selected ?: return delegate.sourceRulesForCall(signature, statement, allRelevant)
        return s.callSource.find(statement)
    }

    override fun sinkRulesForCall(
        signature: GoFunctionSignature,
        statement: GoIRInst,
    ): List<TaintRule.Sink> {
        val s = selected ?: return delegate.sinkRulesForCall(signature, statement)
        return s.callSink.find(statement)
    }

    override fun passThroughRulesForCall(
        signature: GoFunctionSignature,
        statement: GoIRInst,
    ): List<TaintRule.PassThrough> = delegate.passThroughRulesForCall(signature, statement)

    override fun cleanerRulesForCall(
        signature: GoFunctionSignature,
        statement: GoIRInst,
        allRelevant: Boolean,
    ): List<TaintRule.Cleaner> = delegate.cleanerRulesForCall(signature, statement, allRelevant)

    private fun <T : GoTaintAction> List<T>.relevantActions(relevant: Set<CommonTaintAction>): List<T>? =
        filter { it in relevant }.takeIf { it.isNotEmpty() }
}
