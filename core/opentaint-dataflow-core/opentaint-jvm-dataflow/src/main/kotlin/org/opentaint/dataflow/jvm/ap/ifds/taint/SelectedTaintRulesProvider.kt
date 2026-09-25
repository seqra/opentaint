package org.opentaint.dataflow.jvm.ap.ifds.taint

import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.taint.ActionableRules
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.AssignMark
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSource
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodEntrySink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.TaintStaticFieldSource
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.IdentityHashMap

/**
 * Filters a [TaintRulesProvider] to the rules the mark-set scan selected
 * (spec §10, gaps G5/G6). For the six restricted queries (entry-point
 * sources, method sources, exit sources, method sinks, entry sinks, exit
 * sinks) it always calls the delegate first and filters *its* answer -
 * never replaces it - so any filtering the delegate itself does (e.g. the
 * exit-sink `initialFacts` gate, G5) is preserved. Pass-through, cleaner and
 * static-field rules, and [selectRules], always delegate: only entry-point,
 * method and exit sources and sinks are restricted.
 *
 * [select] installs an immutable snapshot; a `null` selection (or a
 * statement outside [ActionableRules]' covered set) means "no filtering".
 */
class SelectedTaintRulesProvider(
    private val delegate: TaintRulesProvider,
) : TaintRulesProvider by delegate {

    /**
     * One statement's `rule -> selected actions` map. The identity map is
     * checked first: on the hot full-scan path the same rule instances the
     * prescan recorded are usually the ones the delegate hands back, so an
     * identity hit avoids the data class' structural `hashCode`/`equals`.
     * The equals-based map is the correctness fallback.
     */
    private class RuleActions(rules: Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>) {
        private val byIdentity = IdentityHashMap<CommonTaintConfigurationItem, Set<CommonTaintAction>>(rules)
        private val byEquals: Map<CommonTaintConfigurationItem, Set<CommonTaintAction>> = rules

        operator fun get(rule: CommonTaintConfigurationItem): Set<CommonTaintAction>? =
            byIdentity[rule] ?: byEquals[rule]

        companion object {
            val EMPTY = RuleActions(emptyMap())
        }
    }

    private class Selection(
        val perStatement: Map<CommonInst, RuleActions>,
        val coveredStatements: Set<CommonInst>,
    )

    @Volatile
    private var selection: Selection? = null

    /** The provider this one filters: the full scan's baseline rules (mark-set debug checks, E2). */
    val unrestricted: TaintRulesProvider get() = delegate

    /** Installs the mark-set scan's selection, or clears it with `rules = null` (Prescan). */
    fun select(rules: ActionableRules?, coveredStatements: Set<CommonInst>) {
        selection = rules?.let { r ->
            Selection(r.mapValues { (_, actions) -> RuleActions(actions) }, coveredStatements)
        }
    }

    /**
     * `null` means "return the delegate's answer unchanged": no selection is
     * installed, [allRelevant] is set, or the statement was never recorded.
     * Otherwise the (possibly empty) per-statement lookup to filter with.
     */
    private fun lookupFor(statement: CommonInst, allRelevant: Boolean): RuleActions? {
        val current = selection ?: return null
        if (allRelevant) return null
        if (statement !in current.coveredStatements) return null
        return current.perStatement[statement] ?: RuleActions.EMPTY
    }

    @Suppress("UNCHECKED_CAST")
    private fun <T : CommonTaintConfigurationItem> restrict(
        statement: CommonInst,
        allRelevant: Boolean,
        base: Iterable<T>,
    ): Iterable<T> {
        val lookup = lookupFor(statement, allRelevant) ?: return base
        return base.mapNotNull { rule ->
            val acts = lookup[rule] ?: return@mapNotNull null
            when (rule) {
                is TaintConfigurationSource ->
                    rule.copyWithActions(rule.actionsAfter.filter { it in acts })
                        .takeIf { it.actionsAfter.isNotEmpty() } as T?
                else -> rule
            }
        }
    }

    private fun TaintConfigurationSource.copyWithActions(actions: List<AssignMark>): TaintConfigurationSource =
        when (this) {
            is TaintEntryPointSource -> copy(actionsAfter = actions)
            is TaintMethodSource -> copy(actionsAfter = actions)
            is TaintMethodExitSource -> copy(actionsAfter = actions)
            is TaintStaticFieldSource -> copy(actionsAfter = actions)
        }

    override fun entryPointRulesForMethod(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        allRelevant: Boolean,
    ): Iterable<TaintEntryPointSource> =
        restrict(statement, allRelevant, delegate.entryPointRulesForMethod(method, statement, fact, allRelevant))

    override fun sourceRulesForMethod(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        allRelevant: Boolean,
    ): Iterable<TaintMethodSource> =
        restrict(statement, allRelevant, delegate.sourceRulesForMethod(method, statement, fact, allRelevant))

    override fun exitSourceRulesForMethod(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        allRelevant: Boolean,
    ): Iterable<TaintMethodExitSource> =
        restrict(statement, allRelevant, delegate.exitSourceRulesForMethod(method, statement, fact, allRelevant))

    override fun sinkRulesForMethod(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        allRelevant: Boolean,
    ): Iterable<TaintMethodSink> =
        restrict(statement, allRelevant, delegate.sinkRulesForMethod(method, statement, fact, allRelevant))

    override fun sinkRulesForMethodEntry(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        allRelevant: Boolean,
    ): Iterable<TaintMethodEntrySink> =
        restrict(statement, allRelevant, delegate.sinkRulesForMethodEntry(method, statement, fact, allRelevant))

    override fun sinkRulesForMethodExit(
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        initialFacts: Set<InitialFactAp>?,
        allRelevant: Boolean,
    ): Iterable<TaintMethodExitSink> =
        restrict(
            statement,
            allRelevant,
            delegate.sinkRulesForMethodExit(method, statement, fact, initialFacts, allRelevant),
        )
}
