package org.opentaint.semgrep.pattern.conversion.go

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedFunctionNameMatcher
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedSimpleNameMatcher
import org.opentaint.dataflow.go.rules.GoTaintConfig
import org.opentaint.dataflow.go.rules.TaintRules
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep

/**
 * LOW-FIDELITY adapter from the SHARED [TaintRuleFromSemgrep] (JVM [SerializedRule]s, produced by
 * the common [org.opentaint.semgrep.pattern.SemgrepRuleLoader] for ALL languages incl. Go) into a
 * [GoTaintConfig].
 *
 * Each rule carries a function-name matcher from which we recover a named function
 * ("pkg.Name" / "util.Source") plus a taint position. The shared loader lowers a semgrep taint
 * rule to a taint AUTOMATON, which it emits as:
 *  - an UNCONDITIONAL [SerializedRule.Source] (condition has no `ContainsMark`) -> a real SOURCE
 *    (its result/taint-assign position becomes tainted);
 *  - a CONDITIONAL [SerializedRule.Source] (condition contains a `ContainsMark`) -> a PROPAGATOR
 *    (the `ContainsMark` position is the `from`, the taint-assign position is the `to`); this is
 *    how `$OUT = util.Wrap($IN)` round-trips;
 *  - a [SerializedRule.Sink] -> a SINK (the first usable `ContainsMark` argument position is the
 *    tainted-argument position);
 *  - a [SerializedRule.PassThrough] -> a PROPAGATOR (rare for Go, but supported).
 *
 * Positions are normalised to what the Go engine understands: `This`/`AnyArgument` collapse to
 * `Argument(0)` (see GoFlowFunctionUtils.resolvePosition, which errors on `This` and maps
 * `AnyArgument` -> arg 0). Other conditions are dropped. Anything that cannot be cleanly named or
 * located is dropped and counted in [dropped] (never thrown). Duplicate rules are de-duplicated.
 */
class GoTaintRuleEmitter {
    /** reason -> number of items dropped for that reason. */
    val dropped = mutableMapOf<String, Int>()

    private fun drop(reason: String): Nothing? {
        dropped[reason] = (dropped[reason] ?: 0) + 1
        return null
    }

    fun emit(ruleId: String, rule: TaintRuleFromSemgrep, mark: String = "taint"): GoTaintConfig {
        val items = rule.taintRules.flatMap { it.rules }
        val sources = items.filterIsInstance<SerializedRule.Source>()

        return GoTaintConfig(
            // Unconditional sources are real sources; conditional ones (carrying a ContainsMark)
            // are propagators.
            sources = sources
                .filter { firstContainsMarkPosition(it.condition) == null }
                .mapNotNull { adaptSource(it, mark) }
                .distinct(),
            sinks = items.filterIsInstance<SerializedRule.Sink>()
                .mapNotNull { adaptSink(it, mark, ruleId) }
                .distinct(),
            propagators = (
                sources
                    .filter { firstContainsMarkPosition(it.condition) != null }
                    .mapNotNull { adaptSourceAsPass(it) } +
                    items.filterIsInstance<SerializedRule.PassThrough>().mapNotNull { adaptPass(it) }
                ).distinct(),
        )
    }

    /** An unconditional source: the function whose taint-assign position becomes tainted. */
    private fun adaptSource(r: SerializedRule.Source, mark: String): TaintRules.Source? {
        val name = qualifiedName(r.function) ?: return drop("source_unnameable")
        val pos = goPosition(r.taint.firstOrNull()?.pos?.base ?: PositionBase.Result)
        return TaintRules.Source(name, mark, pos)
    }

    /** A conditional source modelled as a propagator: ContainsMark position -> taint-assign position. */
    private fun adaptSourceAsPass(r: SerializedRule.Source): TaintRules.Pass? {
        val name = qualifiedName(r.function) ?: return drop("pass_unnameable")
        val from = firstContainsMarkPosition(r.condition) ?: return drop("pass_no_from")
        val to = r.taint.firstOrNull()?.pos?.base ?: PositionBase.Result
        return TaintRules.Pass(name, baseOnly(from), baseOnly(to))
    }

    /** A sink: the function whose tainted ARGUMENT (the first usable ContainsMark) is the sink. */
    private fun adaptSink(r: SerializedRule.Sink, mark: String, ruleId: String): TaintRules.Sink? {
        val name = qualifiedName(r.function) ?: return drop("sink_unnameable")
        val pos = firstContainsMarkPosition(r.condition)?.let { goPosition(it) } ?: PositionBase.Argument(0)
        return TaintRules.Sink(name, mark, pos, r.id ?: ruleId)
    }

    /** A propagator rule: from/to taken from the first copy action. */
    private fun adaptPass(r: SerializedRule.PassThrough): TaintRules.Pass? {
        val name = qualifiedName(r.function) ?: return drop("pass_unnameable")
        val action = r.copy.firstOrNull() ?: return drop("pass_no_copy")
        return TaintRules.Pass(name, normalize(action.from), normalize(action.to))
    }

    /** Reconstruct "pkg.Name" / "util.Source" from a function-name matcher (Simple parts only). */
    private fun qualifiedName(fn: SerializedFunctionNameMatcher): String? {
        val pkg = (fn.`package` as? SerializedSimpleNameMatcher.Simple)?.value
        val cls = (fn.`class` as? SerializedSimpleNameMatcher.Simple)?.value
        val nm = (fn.name as? SerializedSimpleNameMatcher.Simple)?.value ?: return null
        val qualifier = listOfNotNull(pkg, cls).filter { it.isNotEmpty() }.joinToString(".")
        return if (qualifier.isEmpty()) nm else "$qualifier.$nm"
    }

    /**
     * Normalise a [PositionBase] to one the Go engine can resolve: `This` and `AnyArgument` both
     * collapse to `Argument(0)` (matching GoFlowFunctionUtils.resolvePosition, which errors on
     * `This`); everything else is unchanged.
     */
    private fun goPosition(pos: PositionBase): PositionBase = when (pos) {
        is PositionBase.This -> PositionBase.Argument(0)
        is PositionBase.AnyArgument -> PositionBase.Argument(0)
        else -> pos
    }

    private fun normalize(pos: PositionBaseWithModifiers): PositionBaseWithModifiers = when (pos) {
        is PositionBaseWithModifiers.BaseOnly -> PositionBaseWithModifiers.BaseOnly(goPosition(pos.base))
        is PositionBaseWithModifiers.WithModifiers ->
            PositionBaseWithModifiers.WithModifiers(goPosition(pos.base), pos.modifiers)
    }

    private fun baseOnly(pos: PositionBase) = PositionBaseWithModifiers.BaseOnly(goPosition(pos))

    /**
     * Recursively walk the [SerializedCondition] tree (And/Or/Not) for the FIRST usable
     * [SerializedCondition.ContainsMark] and return its position. A `This` ContainsMark is skipped
     * in favour of a real argument position when one exists (the shared loader emits both a
     * receiver-tainted and an argument-tainted variant for a 1-arg call). Returns null if there is
     * no ContainsMark at all.
     */
    private fun firstContainsMarkPosition(cond: SerializedCondition?): PositionBase? {
        if (cond == null) return null
        val positions = collectContainsMarkPositions(cond)
        return positions.firstOrNull { it !is PositionBase.This } ?: positions.firstOrNull()
    }

    private fun collectContainsMarkPositions(cond: SerializedCondition): List<PositionBase> = when (cond) {
        is SerializedCondition.ContainsMark -> listOf(cond.pos.base)
        is SerializedCondition.And -> cond.allOf.flatMap { collectContainsMarkPositions(it) }
        is SerializedCondition.Or -> cond.anyOf.flatMap { collectContainsMarkPositions(it) }
        is SerializedCondition.Not -> collectContainsMarkPositions(cond.not)
        else -> emptyList()
    }
}
