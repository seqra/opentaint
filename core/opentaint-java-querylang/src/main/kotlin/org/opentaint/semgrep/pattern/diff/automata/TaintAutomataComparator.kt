package org.opentaint.semgrep.pattern.diff.automata

import org.opentaint.semgrep.pattern.conversion.MetavarAtom
import org.opentaint.semgrep.pattern.conversion.taint.TaintAutomataEdges
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata.Edge
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata.EdgeCondition
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata.EdgeEffect
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata.MethodPredicate
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata.State
import org.opentaint.semgrep.pattern.conversion.taint.TaintRuleEdge

/** Result of comparing two generated taint automata. */
sealed interface TaintAutomataComparison {
    data object Equivalent : TaintAutomataComparison

    data class Different(
        val witnesses: List<AutomataTraceWitness>,
    ) : TaintAutomataComparison {
        init {
            require(witnesses.isNotEmpty())
        }
    }

    data class Inconclusive(
        val reason: AutomataInconclusiveReason,
        val detail: String? = null,
    ) : TaintAutomataComparison
}

enum class AutomataInconclusiveReason {
    UNSUPPORTED_NONDETERMINISTIC_REGISTER_AUTOMATON,
    PRODUCT_LIMIT_REACHED,
    CUBE_COMPILATION_FAILED,
    VARIANT_COUNT_MISMATCH,
}

enum class AutomataTraceDirection { OLD_ONLY, NEW_ONLY }

enum class AutomataTraceObservation {
    ACCEPT,
    DEAD,
    TRANSITION,
    GENERATED_EDGE,
    METAVAR_INFO,
}

enum class AutomataEventKind { METHOD_ENTER, METHOD_CALL, METHOD_EXIT, ANALYSIS_END }

data class AutomataTraceStep(
    val eventKind: AutomataEventKind,
    /** Stable, human-oriented rendering. It deliberately contains user metavariable names. */
    val label: String,
    val oldStateId: Int?,
    val newStateId: Int?,
    val oldDestinationStateId: Int?,
    val newDestinationStateId: Int?,
)

data class AutomataTraceWitness(
    val direction: AutomataTraceDirection,
    val observation: AutomataTraceObservation,
    val steps: List<AutomataTraceStep>,
    val detail: String,
)

data class TaintAutomataComparisonLimits(
    val maxProductConfigurations: Int = 10_000,
) {
    init {
        require(maxProductConfigurations > 0)
    }
}

/**
 * Strict-label synchronous comparison for [TaintAutomataEdges].
 *
 * Generated state numbers and register assignment epochs are alpha-renamed. User metavariable
 * names, predicates, transition kinds, conditions and effects are compared literally. The current
 * implementation considers transitions with the same exact normalized label nondeterministic when
 * they lead to different states; it does not attempt guard satisfiability or alpha-renaming of user
 * metavariables.
 */
class TaintAutomataComparator(
    private val limits: TaintAutomataComparisonLimits = TaintAutomataComparisonLimits(),
) {
    /** Returns a deterministic symbolic witness for an automaton added to or removed from a rule. */
    fun sampleAgainstEmpty(
        automata: TaintAutomataEdges,
        direction: AutomataTraceDirection,
    ): AutomataTraceWitness? {
        val initial = automata.automata.initial
        if (initial in automata.automata.finalAcceptStates) {
            return AutomataTraceWitness(
                direction,
                AutomataTraceObservation.ACCEPT,
                emptyList(),
                "Only this side accepts the empty event trace",
            )
        }
        if (initial in automata.automata.finalDeadStates) {
            return AutomataTraceWitness(
                direction,
                AutomataTraceObservation.DEAD,
                emptyList(),
                "Only this side reaches a dead state on the empty event trace",
            )
        }

        val first = normalizedOutgoing(automata.automata, initial)
            .sortedBy { it.label.display() }
            .firstOrNull() ?: return null
        val step = AutomataTraceStep(
            eventKind = first.label.kind,
            label = first.label.display(),
            oldStateId = initial.id.takeIf { direction == AutomataTraceDirection.OLD_ONLY },
            newStateId = initial.id.takeIf { direction == AutomataTraceDirection.NEW_ONLY },
            oldDestinationStateId = first.destination.id.takeIf { direction == AutomataTraceDirection.OLD_ONLY },
            newDestinationStateId = first.destination.id.takeIf { direction == AutomataTraceDirection.NEW_ONLY },
        )
        return AutomataTraceWitness(
            direction,
            AutomataTraceObservation.TRANSITION,
            listOf(step),
            "Only this side contains the sampled transition",
        )
    }

    fun compare(old: TaintAutomataEdges, new: TaintAutomataEdges): TaintAutomataComparison {
        compareMetaVarInfo(old, new)?.let { return it }

        val initialEpochs = EpochCorrespondence.empty().align(
            old.automata.initial,
            new.automata.initial,
        ) ?: return registerDifference(emptyList(), old.automata.initial, new.automata.initial)

        val queue = ArrayDeque<ProductConfiguration>()
        queue.add(ProductConfiguration(old.automata.initial, new.automata.initial, initialEpochs, emptyList()))
        val visited = hashSetOf<ProductKey>()

        while (queue.isNotEmpty()) {
            val configuration = queue.removeFirst()
            if (!visited.add(configuration.key())) continue
            if (visited.size > limits.maxProductConfigurations) {
                return TaintAutomataComparison.Inconclusive(
                    AutomataInconclusiveReason.PRODUCT_LIMIT_REACHED,
                    "Reached ${limits.maxProductConfigurations} synchronous product configurations",
                )
            }

            terminalDifferences(old, new, configuration)?.let { return it }
            globalStateDifferences(old, new, configuration)?.let { return it }

            val oldOutgoing = normalizedOutgoing(old.automata, configuration.oldState)
            val newOutgoing = normalizedOutgoing(new.automata, configuration.newState)

            nondeterminism(oldOutgoing, "old", configuration.oldState)?.let { return it }
            nondeterminism(newOutgoing, "new", configuration.newState)?.let { return it }

            val oldByLabel = oldOutgoing.associateBy { it.label }
            val newByLabel = newOutgoing.associateBy { it.label }
            val labels = (oldByLabel.keys + newByLabel.keys).sortedBy(EdgeLabel::display)

            val missingWitnesses = mutableListOf<AutomataTraceWitness>()
            for (label in labels) {
                val oldTransition = oldByLabel[label]
                val newTransition = newByLabel[label]
                if (oldTransition == null || newTransition == null) {
                    val direction = if (oldTransition != null) {
                        AutomataTraceDirection.OLD_ONLY
                    } else {
                        AutomataTraceDirection.NEW_ONLY
                    }
                    missingWitnesses += witness(
                        configuration,
                        direction,
                        AutomataTraceObservation.TRANSITION,
                        oldTransition,
                        newTransition,
                        "Only the ${direction.name.lowercase().replace('_', ' ')} automaton has this transition",
                    )
                    continue
                }

                projectionDifferences(old, new, configuration, oldTransition, newTransition)
                    ?.let { return it }

                val nextEpochs = configuration.epochs.align(oldTransition.destination, newTransition.destination)
                    ?: return registerDifference(
                        configuration.steps + traceStep(configuration, oldTransition, newTransition),
                        oldTransition.destination,
                        newTransition.destination,
                    )

                queue.add(
                    ProductConfiguration(
                        oldTransition.destination,
                        newTransition.destination,
                        nextEpochs,
                        configuration.steps + traceStep(configuration, oldTransition, newTransition),
                    )
                )
            }
            if (missingWitnesses.isNotEmpty()) {
                return TaintAutomataComparison.Different(
                    missingWitnesses
                        .distinctBy { it.direction to it.observation }
                        .sortedBy { it.direction.ordinal },
                )
            }
        }

        return TaintAutomataComparison.Equivalent
    }

    private fun compareMetaVarInfo(
        old: TaintAutomataEdges,
        new: TaintAutomataEdges,
    ): TaintAutomataComparison.Different? {
        if (old.metaVarInfo == new.metaVarInfo) return null
        val oldKeys = old.metaVarInfo.constraints.keys
        val newKeys = new.metaVarInfo.constraints.keys
        val witnesses = mutableListOf<AutomataTraceWitness>()
        if ((oldKeys - newKeys).isNotEmpty() || oldKeys == newKeys) {
            witnesses += AutomataTraceWitness(
                AutomataTraceDirection.OLD_ONLY,
                AutomataTraceObservation.METAVAR_INFO,
                emptyList(),
                "Old metavariable constraints differ: ${oldKeys.sorted()}",
            )
        }
        if ((newKeys - oldKeys).isNotEmpty() || oldKeys == newKeys) {
            witnesses += AutomataTraceWitness(
                AutomataTraceDirection.NEW_ONLY,
                AutomataTraceObservation.METAVAR_INFO,
                emptyList(),
                "New metavariable constraints differ: ${newKeys.sorted()}",
            )
        }
        return TaintAutomataComparison.Different(witnesses)
    }

    private fun terminalDifferences(
        old: TaintAutomataEdges,
        new: TaintAutomataEdges,
        configuration: ProductConfiguration,
    ): TaintAutomataComparison.Different? {
        val witnesses = mutableListOf<AutomataTraceWitness>()
        terminalWitnesses(
            witnesses,
            configuration,
            AutomataTraceObservation.ACCEPT,
            configuration.oldState in old.automata.finalAcceptStates,
            configuration.newState in new.automata.finalAcceptStates,
        )
        terminalWitnesses(
            witnesses,
            configuration,
            AutomataTraceObservation.DEAD,
            configuration.oldState in old.automata.finalDeadStates,
            configuration.newState in new.automata.finalDeadStates,
        )
        return witnesses.takeIf { it.isNotEmpty() }?.let { TaintAutomataComparison.Different(it) }
    }

    private fun terminalWitnesses(
        destination: MutableList<AutomataTraceWitness>,
        configuration: ProductConfiguration,
        observation: AutomataTraceObservation,
        oldValue: Boolean,
        newValue: Boolean,
    ) {
        if (oldValue == newValue) return
        destination += AutomataTraceWitness(
            if (oldValue) AutomataTraceDirection.OLD_ONLY else AutomataTraceDirection.NEW_ONLY,
            observation,
            configuration.steps,
            "The trace reaches a ${observation.name.lowercase()} state on only one side",
        )
    }

    private fun globalStateDifferences(
        old: TaintAutomataEdges,
        new: TaintAutomataEdges,
        configuration: ProductConfiguration,
    ): TaintAutomataComparison.Different? {
        val oldAssign = configuration.oldState in old.globalStateAssignStates
        val newAssign = configuration.newState in new.globalStateAssignStates
        if (oldAssign == newAssign) return null
        return TaintAutomataComparison.Different(
            listOf(
                AutomataTraceWitness(
                    if (oldAssign) AutomataTraceDirection.OLD_ONLY else AutomataTraceDirection.NEW_ONLY,
                    AutomataTraceObservation.GENERATED_EDGE,
                    configuration.steps,
                    "Only one side assigns global state at the reached state",
                )
            )
        )
    }

    private fun projectionDifferences(
        old: TaintAutomataEdges,
        new: TaintAutomataEdges,
        configuration: ProductConfiguration,
        oldTransition: NormalizedTransition,
        newTransition: NormalizedTransition,
    ): TaintAutomataComparison.Different? {
        val oldProjection = projection(old, configuration.oldState, oldTransition)
        val newProjection = projection(new, configuration.newState, newTransition)
        if (oldProjection == newProjection) return null

        val witnesses = mutableListOf<AutomataTraceWitness>()
        if ((oldProjection - newProjection).isNotEmpty()) {
            witnesses += witness(
                configuration,
                AutomataTraceDirection.OLD_ONLY,
                AutomataTraceObservation.GENERATED_EDGE,
                oldTransition,
                newTransition,
                "Generated edge projection differs: old=$oldProjection, new=$newProjection",
            )
        }
        if ((newProjection - oldProjection).isNotEmpty()) {
            witnesses += witness(
                configuration,
                AutomataTraceDirection.NEW_ONLY,
                AutomataTraceObservation.GENERATED_EDGE,
                oldTransition,
                newTransition,
                "Generated edge projection differs: old=$oldProjection, new=$newProjection",
            )
        }
        return TaintAutomataComparison.Different(witnesses)
    }

    private fun projection(
        automata: TaintAutomataEdges,
        source: State,
        transition: NormalizedTransition,
    ): Set<ProjectionObservation> {
        val result = linkedSetOf<ProjectionObservation>()
        fun collect(category: ProjectionCategory, edges: List<TaintRuleEdge>) {
            edges.asSequence()
                .filter { it.stateFrom == source && it.stateTo == transition.destination }
                .filter { it.label() == transition.label }
                .mapTo(result) { ProjectionObservation(category, it.checkGlobalState) }
        }
        collect(ProjectionCategory.ORDINARY, automata.edges)
        collect(ProjectionCategory.FINAL_ACCEPT, automata.edgesToFinalAccept)
        collect(ProjectionCategory.FINAL_DEAD, automata.edgesToFinalDead)
        return result
    }

    private fun normalizedOutgoing(automata: TaintRegisterStateAutomata, state: State): List<NormalizedTransition> =
        automata.successors[state].orEmpty()
            .map { (edge, destination) -> NormalizedTransition(edge.label(), destination) }
            .sortedBy { it.label.display() + " -> " + it.destination.id }

    private fun nondeterminism(
        outgoing: List<NormalizedTransition>,
        side: String,
        state: State,
    ): TaintAutomataComparison.Inconclusive? {
        val ambiguous = outgoing.groupBy { it.label }.entries.firstOrNull { (_, transitions) ->
            transitions.map { it.destination }.distinct().size > 1
        } ?: return null
        return TaintAutomataComparison.Inconclusive(
            AutomataInconclusiveReason.UNSUPPORTED_NONDETERMINISTIC_REGISTER_AUTOMATON,
            "$side state ${state.id} has multiple destinations for ${ambiguous.key.display()}",
        )
    }

    private fun registerDifference(
        steps: List<AutomataTraceStep>,
        oldState: State,
        newState: State,
    ): TaintAutomataComparison.Different {
        val detail = "Register layouts cannot be alpha-corresponded: " +
            "old=${oldState.register.display()}, new=${newState.register.display()}"
        val oldKeys = oldState.register.assignedVars.keys
        val newKeys = newState.register.assignedVars.keys
        val directions = buildSet {
            if ((oldKeys - newKeys).isNotEmpty()) add(AutomataTraceDirection.OLD_ONLY)
            if ((newKeys - oldKeys).isNotEmpty()) add(AutomataTraceDirection.NEW_ONLY)
            if (isEmpty()) addAll(AutomataTraceDirection.entries)
        }
        return TaintAutomataComparison.Different(
            directions.map {
                AutomataTraceWitness(it, AutomataTraceObservation.TRANSITION, steps, detail)
            }
        )
    }

    private fun witness(
        configuration: ProductConfiguration,
        direction: AutomataTraceDirection,
        observation: AutomataTraceObservation,
        oldTransition: NormalizedTransition?,
        newTransition: NormalizedTransition?,
        detail: String,
    ) = AutomataTraceWitness(
        direction,
        observation,
        configuration.steps + traceStep(configuration, oldTransition, newTransition),
        detail,
    )

    private fun traceStep(
        configuration: ProductConfiguration,
        oldTransition: NormalizedTransition?,
        newTransition: NormalizedTransition?,
    ): AutomataTraceStep {
        val label = oldTransition?.label ?: checkNotNull(newTransition).label
        return AutomataTraceStep(
            label.kind,
            label.display(),
            oldTransition?.let { configuration.oldState.id },
            newTransition?.let { configuration.newState.id },
            oldTransition?.destination?.id,
            newTransition?.destination?.id,
        )
    }
}

private data class ProductConfiguration(
    val oldState: State,
    val newState: State,
    val epochs: EpochCorrespondence,
    val steps: List<AutomataTraceStep>,
) {
    fun key() = ProductKey(oldState, newState, epochs)
}

private data class ProductKey(
    val oldState: State,
    val newState: State,
    val epochs: EpochCorrespondence,
)

private data class EpochCorrespondence(
    val oldToNew: Map<Int, Int>,
    val newToOld: Map<Int, Int>,
) {
    fun align(oldState: State, newState: State): EpochCorrespondence? {
        val oldRegisters = oldState.register.assignedVars
        val newRegisters = newState.register.assignedVars
        if (oldRegisters.keys != newRegisters.keys) return null

        val nextOldToNew = oldToNew.toMutableMap()
        val nextNewToOld = newToOld.toMutableMap()
        for (metavar in oldRegisters.keys.sortedBy(MetavarAtom::toString)) {
            val oldEpoch = checkNotNull(oldRegisters[metavar])
            val newEpoch = checkNotNull(newRegisters[metavar])
            if (nextOldToNew[oldEpoch]?.let { it != newEpoch } == true) return null
            if (nextNewToOld[newEpoch]?.let { it != oldEpoch } == true) return null
            nextOldToNew[oldEpoch] = newEpoch
            nextNewToOld[newEpoch] = oldEpoch
        }
        return EpochCorrespondence(nextOldToNew, nextNewToOld)
    }

    companion object {
        fun empty() = EpochCorrespondence(emptyMap(), emptyMap())
    }
}

private data class NormalizedTransition(
    val label: EdgeLabel,
    val destination: State,
)

private data class EdgeLabel(
    val kind: AutomataEventKind,
    val condition: ConditionLabel,
    val effect: EffectLabel,
) {
    fun display(): String = buildString {
        append(kind.name)
        if (condition != ConditionLabel.EMPTY) append(" if ").append(condition.display())
        if (effect != EffectLabel.EMPTY) append(" assign ").append(effect.display())
    }
}

private data class ConditionLabel(
    val readMetaVar: Map<MetavarAtom, Set<MethodPredicate>>,
    val other: Set<MethodPredicate>,
) {
    fun display(): String = buildList {
        readMetaVar.entries.sortedBy { it.key.toString() }.forEach { (metavar, predicates) ->
            add("$metavar:[${predicates.display()}]")
        }
        if (other.isNotEmpty()) add("other:[${other.display()}]")
    }.joinToString(",")

    companion object {
        val EMPTY = ConditionLabel(emptyMap(), emptySet())
    }
}

private data class EffectLabel(
    val assignMetaVar: Map<MetavarAtom, Set<MethodPredicate>>,
) {
    fun display(): String = assignMetaVar.entries.sortedBy { it.key.toString() }
        .joinToString(",") { (metavar, predicates) -> "$metavar:[${predicates.display()}]" }

    companion object {
        val EMPTY = EffectLabel(emptyMap())
    }
}

private fun Collection<MethodPredicate>.display(): String =
    sortedBy { it.toString() }.joinToString("&")

private fun EdgeCondition.label() = ConditionLabel(
    readMetaVar.mapValues { (_, predicates) -> predicates.toSet() },
    other.toSet(),
)

private fun EdgeEffect.label() = EffectLabel(
    assignMetaVar.mapValues { (_, predicates) -> predicates.toSet() },
)

private fun Edge.label(): EdgeLabel = when (this) {
    is Edge.MethodEnter -> EdgeLabel(AutomataEventKind.METHOD_ENTER, condition.label(), effect.label())
    is Edge.MethodCall -> EdgeLabel(AutomataEventKind.METHOD_CALL, condition.label(), effect.label())
    is Edge.MethodExit -> EdgeLabel(AutomataEventKind.METHOD_EXIT, condition.label(), effect.label())
    is Edge.AnalysisEnd -> EdgeLabel(AutomataEventKind.ANALYSIS_END, ConditionLabel.EMPTY, EffectLabel.EMPTY)
}

private fun TaintRuleEdge.label(): EdgeLabel {
    val kind = when (edgeKind) {
        TaintRuleEdge.Kind.MethodEnter -> AutomataEventKind.METHOD_ENTER
        TaintRuleEdge.Kind.MethodCall -> AutomataEventKind.METHOD_CALL
        TaintRuleEdge.Kind.MethodExit -> AutomataEventKind.METHOD_EXIT
    }
    return EdgeLabel(kind, edgeCondition.label(), edgeEffect.label())
}

private fun TaintRegisterStateAutomata.StateRegister.display(): String = assignedVars.entries
    .sortedBy { it.key.toString() }
    .joinToString(prefix = "{", postfix = "}") { (metavar, epoch) -> "$metavar=$epoch" }

private enum class ProjectionCategory { ORDINARY, FINAL_ACCEPT, FINAL_DEAD }

private data class ProjectionObservation(
    val category: ProjectionCategory,
    val checkGlobalState: Boolean,
)
