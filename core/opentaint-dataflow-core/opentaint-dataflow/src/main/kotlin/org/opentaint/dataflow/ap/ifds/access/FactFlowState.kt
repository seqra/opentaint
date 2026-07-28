package org.opentaint.dataflow.ap.ifds.access

import kotlinx.collections.immutable.PersistentSet
import kotlinx.collections.immutable.persistentHashSetOf
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor

/**
 * Cleaner effects that still have to be enforced when an abstract fact materializes.
 *
 * This is deliberately separate from [ExclusionSet]: exclusions partition demand-driven fact
 * analysis, while these marks are semantic effects produced by starred cleaners.
 */
class DeepCleanEffects private constructor(
    private val marks: PersistentSet<TaintMarkAccessor>,
) {
    val isEmpty: Boolean get() = marks.isEmpty()
    val size: Int get() = marks.size

    operator fun contains(mark: TaintMarkAccessor): Boolean = mark in marks

    fun add(mark: TaintMarkAccessor): DeepCleanEffects {
        val added = marks.add(mark)
        return if (added === marks) this else DeepCleanEffects(added)
    }

    fun forEach(action: (TaintMarkAccessor) -> Unit) = marks.forEach(action)

    internal infix fun then(other: DeepCleanEffects): DeepCleanEffects {
        val composed = marks.addAll(other.marks)
        return if (composed === marks) this else DeepCleanEffects(composed)
    }

    internal infix fun join(other: DeepCleanEffects): DeepCleanEffects {
        val shared = marks.retainAll(other.marks)
        return when {
            shared === marks -> this
            shared.isEmpty() -> Empty
            else -> DeepCleanEffects(shared)
        }
    }

    override fun equals(other: Any?): Boolean =
        this === other || other is DeepCleanEffects && marks == other.marks

    override fun hashCode(): Int = marks.hashCode()

    override fun toString(): String =
        marks.joinToString(prefix = "deepClean{", postfix = "}") { it.mark }

    companion object {
        val Empty = DeepCleanEffects(persistentHashSetOf())
    }
}

/**
 * Universal state carried by an IFDS fact edge.
 *
 * [then] is sequential composition: both refinements and both cleaner effects happened.
 * [join] combines alternative executions: analysis exclusions remain partitioned elsewhere and
 * therefore union, while a cleaner effect remains true only if every alternative performed it.
 *
 * Access-path representations decide how cleaner effects are stored. Tree facts normally keep
 * them structurally on abstract nodes and therefore carry [DeepCleanEffects.Empty] here; Automata
 * and Cactus currently use this edge-level representation.
 */
data class FactFlowState(
    val exclusions: ExclusionSet,
    val deepCleanEffects: DeepCleanEffects = DeepCleanEffects.Empty,
) {
    init {
        check(exclusions !is ExclusionSet.Universe || deepCleanEffects.isEmpty) {
            "Universe facts cannot carry cleaner effects"
        }
    }

    infix fun then(other: FactFlowState): FactFlowState {
        val composedExclusions = exclusions.union(other.exclusions)
        if (composedExclusions is ExclusionSet.Universe) return Universe

        val composedEffects = deepCleanEffects then other.deepCleanEffects
        return when {
            composedExclusions === exclusions && composedEffects === deepCleanEffects -> this
            composedExclusions === other.exclusions && composedEffects === other.deepCleanEffects -> other
            else -> FactFlowState(composedExclusions, composedEffects)
        }
    }

    infix fun join(other: FactFlowState): FactFlowState {
        val joinedExclusions = exclusions.union(other.exclusions)
        if (joinedExclusions is ExclusionSet.Universe) return Universe

        val joinedEffects = deepCleanEffects join other.deepCleanEffects
        return when {
            joinedExclusions === exclusions && joinedEffects === deepCleanEffects -> this
            joinedExclusions === other.exclusions && joinedEffects === other.deepCleanEffects -> other
            else -> FactFlowState(joinedExclusions, joinedEffects)
        }
    }

    fun exclude(accessor: org.opentaint.dataflow.ap.ifds.Accessor): FactFlowState =
        withExclusions(exclusions.add(accessor))

    fun withExclusions(exclusions: ExclusionSet): FactFlowState = when {
        exclusions is ExclusionSet.Universe -> Universe
        exclusions === this.exclusions -> this
        else -> FactFlowState(exclusions, deepCleanEffects)
    }

    fun cleanDeep(mark: TaintMarkAccessor): FactFlowState {
        if (exclusions is ExclusionSet.Universe) return this
        val effects = deepCleanEffects.add(mark)
        return if (effects === deepCleanEffects) this else FactFlowState(exclusions, effects)
    }

    companion object {
        val Empty = FactFlowState(ExclusionSet.Empty)
        val Universe = FactFlowState(ExclusionSet.Universe)
    }
}
