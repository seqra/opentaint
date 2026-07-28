package org.opentaint.dataflow.ap.ifds.access

import kotlinx.collections.immutable.PersistentSet
import kotlinx.collections.immutable.persistentHashSetOf
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor

/**
 * Residual cleaner effects used by access representations that encode any-field abstraction as a
 * single growable region.
 *
 * This is a dedicated Automata/Cactus representation detail, not demand-analysis state.
 */
class AnyFieldCleanerEffects private constructor(
    private val marks: PersistentSet<TaintMarkAccessor>,
) {
    val isEmpty: Boolean get() = marks.isEmpty()
    val size: Int get() = marks.size

    operator fun contains(mark: TaintMarkAccessor): Boolean = mark in marks

    fun add(mark: TaintMarkAccessor): AnyFieldCleanerEffects {
        val added = marks.add(mark)
        return if (added === marks) this else AnyFieldCleanerEffects(added)
    }

    fun forEach(action: (TaintMarkAccessor) -> Unit) = marks.forEach(action)

    internal infix fun then(other: AnyFieldCleanerEffects): AnyFieldCleanerEffects {
        val composed = marks.addAll(other.marks)
        return when {
            composed === marks -> this
            composed == other.marks -> other
            else -> AnyFieldCleanerEffects(composed)
        }
    }

    internal infix fun join(other: AnyFieldCleanerEffects): AnyFieldCleanerEffects {
        val shared = marks.retainAll(other.marks)
        return when {
            shared === marks -> this
            shared == other.marks -> other
            shared.isEmpty() -> Empty
            else -> AnyFieldCleanerEffects(shared)
        }
    }

    override fun equals(other: Any?): Boolean =
        this === other || other is AnyFieldCleanerEffects && marks == other.marks

    override fun hashCode(): Int = marks.hashCode()

    override fun toString(): String =
        marks.joinToString(prefix = "cleanAnyField{", postfix = "}") { it.mark }

    companion object {
        val Empty = AnyFieldCleanerEffects(persistentHashSetOf())
    }
}

internal fun AnyFieldCleanerEffects.forExclusions(exclusions: ExclusionSet): AnyFieldCleanerEffects =
    if (exclusions is ExclusionSet.Universe) AnyFieldCleanerEffects.Empty else this

/**
 * Complete semantic access value for representations with one growable any-field region.
 *
 * Summary code treats this value opaquely: the graph/cactus and the cleaner effect cannot be
 * separated without changing the represented fact.
 */
data class AnyFieldAccess<A>(
    val access: A,
    val cleanerEffects: AnyFieldCleanerEffects,
)
