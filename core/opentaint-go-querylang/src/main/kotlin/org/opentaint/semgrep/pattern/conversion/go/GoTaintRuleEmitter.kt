package org.opentaint.semgrep.pattern.conversion.go

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.go.rules.GoTaintConfig
import org.opentaint.dataflow.go.rules.TaintRules
import org.opentaint.semgrep.pattern.SemgrepTaintPropagator
import org.opentaint.semgrep.pattern.SemgrepTaintRule
import org.opentaint.semgrep.pattern.conversion.IsMetavar
import org.opentaint.semgrep.pattern.conversion.MetavarAtom
import org.opentaint.semgrep.pattern.conversion.ParamCondition
import org.opentaint.semgrep.pattern.conversion.ParamConstraint
import org.opentaint.semgrep.pattern.conversion.ParamPosition
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternActionList

/**
 * LOW-FIDELITY lowering of taint patterns (already converted to the shared action-list model)
 * into a [GoTaintConfig].
 *
 * Works DIRECTLY from the action lists (not the taint automaton): the source/sink/pass each carry a
 * single [SemgrepPatternAction.MethodCall] from which we recover a named function + a taint position.
 * Conditions (argument types/values) are intentionally dropped. Anything that cannot be cleanly
 * named or located is dropped and counted in [dropped] (never thrown).
 */
class GoTaintRuleEmitter {
    /** reason -> number of items dropped for that reason. */
    val dropped = mutableMapOf<String, Int>()

    private fun drop(reason: String): Nothing? {
        dropped[reason] = (dropped[reason] ?: 0) + 1
        return null
    }

    /** The single [SemgrepPatternAction.MethodCall] in a simple source/sink/pass action list, or null. */
    private fun primaryCall(list: SemgrepPatternActionList): SemgrepPatternAction.MethodCall? =
        list.actions.singleOrNull() as? SemgrepPatternAction.MethodCall

    /** A source: the function whose RESULT is tainted. */
    fun emitSource(list: SemgrepPatternActionList, mark: String): TaintRules.Source? {
        val call = primaryCall(list) ?: return drop("source_not_single_call")
        val name = goQualifiedName(call.methodName, call.enclosingClassName) ?: return drop("source_unnameable")
        return TaintRules.Source(name, mark, PositionBase.Result)
    }

    /** A sink: the function whose tainted ARGUMENT (the IsMetavar param) is the sink position. */
    fun emitSink(list: SemgrepPatternActionList, mark: String, ruleId: String): TaintRules.Sink? {
        val call = primaryCall(list) ?: return drop("sink_not_single_call")
        val name = goQualifiedName(call.methodName, call.enclosingClassName) ?: return drop("sink_unnameable")
        val pos = sinkPosition(call) ?: return drop("sink_no_tainted_position")
        return TaintRules.Sink(name, mark, pos, ruleId)
    }

    /** A propagator: from/to are metavar NAMES; locate each in the call's obj/params/result. */
    fun emitPass(prop: SemgrepTaintPropagator<SemgrepPatternActionList>): TaintRules.Pass? {
        val call = primaryCall(prop.pattern) ?: return drop("pass_not_single_call")
        val name = goQualifiedName(call.methodName, call.enclosingClassName) ?: return drop("pass_unnameable")
        val from = positionOfMetavar(call, prop.from) ?: return drop("pass_from_not_found")
        val to = positionOfMetavar(call, prop.to) ?: return drop("pass_to_not_found")
        return TaintRules.Pass(
            name,
            PositionBaseWithModifiers.BaseOnly(from),
            PositionBaseWithModifiers.BaseOnly(to),
        )
    }

    fun emit(
        ruleId: String,
        rule: SemgrepTaintRule<SemgrepPatternActionList>,
        mark: String = "taint",
    ): GoTaintConfig =
        GoTaintConfig(
            sources = rule.sources.mapNotNull { emitSource(it.pattern, mark) },
            sinks = rule.sinks.mapNotNull { emitSink(it.pattern, mark, ruleId) },
            propagators = rule.propagators.mapNotNull { emitPass(it) },
        )

    /**
     * The taint position of a sink call: the FIRST argument whose condition carries a metavar
     * becomes that argument position; if no argument carries one but the receiver does, the receiver
     * (`PositionBase.This`) is used. Otherwise null (no tainted position).
     */
    private fun sinkPosition(call: SemgrepPatternAction.MethodCall): PositionBase? {
        val argPos = firstMetavarArgPosition(call.params) { it.metavarNames().isNotEmpty() }
        if (argPos != null) return argPos
        if (call.obj?.metavarNames()?.isNotEmpty() == true) return PositionBase.This
        return null
    }

    /**
     * The position (within [call]) of the argument/receiver/result carrying the metavar named
     * [metaName], or null if it appears nowhere locatable.
     */
    private fun positionOfMetavar(call: SemgrepPatternAction.MethodCall, metaName: String): PositionBase? {
        if (call.obj?.metavarNames()?.contains(metaName) == true) return PositionBase.This
        if (call.result?.metavarNames()?.contains(metaName) == true) return PositionBase.Result
        return firstMetavarArgPosition(call.params) { it.metavarNames().contains(metaName) }
    }

    /**
     * Position of the first argument whose condition satisfies [predicate].
     *
     * For [ParamConstraint.Concrete] the list index is the argument index. For
     * [ParamConstraint.Partial] the [ParamPosition] is mapped: Concrete(idx) -> Argument(idx),
     * Any(classifier) -> AnyArgument(classifier), Named(field) -> AnyArgument(field).
     */
    private fun firstMetavarArgPosition(
        params: ParamConstraint,
        predicate: (ParamCondition) -> Boolean,
    ): PositionBase? = when (params) {
        is ParamConstraint.Concrete -> {
            val idx = params.params.indexOfFirst { predicate(it) }
            if (idx >= 0) PositionBase.Argument(idx) else null
        }

        is ParamConstraint.Partial -> {
            val match = params.params.firstOrNull { predicate(it.condition) }
            when (val pos = match?.position) {
                is ParamPosition.Concrete -> PositionBase.Argument(pos.idx)
                is ParamPosition.Any -> PositionBase.AnyArgument(pos.paramClassifier)
                is ParamPosition.Named -> PositionBase.AnyArgument(pos.field)
                null -> null
            }
        }
    }
}

/**
 * Names of all metavars referenced by this condition.
 *
 * Unwraps [ParamCondition.And] and reads [IsMetavar], expanding both [MetavarAtom.Basic] and
 * [MetavarAtom.Complex] (whose component basics are flattened).
 */
internal fun ParamCondition.metavarNames(): Set<String> = when (this) {
    is ParamCondition.And -> conditions.flatMapTo(mutableSetOf()) { it.metavarNames() }
    is IsMetavar -> metavar.basics.mapTo(mutableSetOf()) { it.name }
    else -> emptySet()
}
