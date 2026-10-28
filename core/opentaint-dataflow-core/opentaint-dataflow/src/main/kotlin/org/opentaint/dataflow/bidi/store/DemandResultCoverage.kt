package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.*
import java.util.concurrent.atomic.AtomicLongArray

/** Counters only. A query never retains its path trace in the frozen snapshot. */
internal class DemandQueryStatistics {
    private val values = AtomicLongArray(12)
    fun add(kind: Int, amount: Long = 1) { values.addAndGet(kind, amount) }
    override fun toString(): String = listOf("c2Direct", "c2Local", "c2Visible", "c2Covered", "c2Roots",
        "c2States", "c2Joins", "c5Candidates", "c5States", "c5Restrict", "c5Covered", "c5Visible")
        .mapIndexed { i, name -> "$name=${values[i]}" }.joinToString(" ")
}

/** Facts equality omits protection. Join only that annotation for exactly equal ordinary payloads. */
internal class ExactDemandResults(private val ap: ApManager, private val ops: ApOps) {
    private val values = LinkedHashMap<Facts, Facts>()
    private var coverage: RawCoverage? = null
    private var coverageChecked = false
    fun add(value: Facts) {
        ap.cancellation.checkpoint()
        val old = values[value]
        values[value] = if (old is TaintTree && value is TaintTree) {
            val mask = when {
                old.nonSubsumable == null -> value.nonSubsumable
                value.nonSubsumable == null -> old.nonSubsumable
                else -> ap.taintAlg.mergeAdd(old.nonSubsumable, value.nonSubsumable, ap.cancellation)
            }
            old.withProtection(mask, ap.cancellation)
        } else old ?: value
        coverage?.add(value)
    }
    fun all(): List<Facts> = values.values.toList()

    /** ANY/MUST must exhaust: another pair can produce a distinct rebased/EXACT result. */
    fun covers(raw: Facts): Boolean {
        if (!coverageChecked) {
            coverageChecked = true
            val leaves = ops.leaves(raw).toList()
            if (leaves.all { it.fact.tail == Tail.STAR || it.fact.tail == Tail.EXACT }) {
                coverage = RawCoverage(raw, leaves)
                for (value in values.values) coverage!!.add(value)
            }
        }
        return coverage?.done == true
    }

    private inner class RawCoverage(private val raw: Facts, leaves: List<Pattern>) {
        private val ordinary = leaves.toHashSet()
        private val protected = (raw as? TaintTree)?.protectedPart()?.let { ops.leaves(it).toHashSet() } ?: HashSet()
        val done: Boolean get() = ordinary.isEmpty() && protected.isEmpty()
        fun add(value: Facts) {
            ap.cancellation.checkpoint()
            if (done || value.base != raw.base || value.layer != raw.layer) return
            if (ordinary.isNotEmpty()) for (leaf in ops.leaves(value)) ordinary.remove(leaf)
            if (protected.isNotEmpty()) (value as? TaintTree)?.protectedPart()?.let { part ->
                for (leaf in ops.leaves(part)) protected.remove(leaf)
            }
        }
    }
}

/** Compare structural keys from the scalar emitter. This check never interns hypothetical APs. */
internal class InitialDemandResults(private val ap: ApManager) {
    val initials = LinkedHashSet<InitialAp>()
    private val keys = HashSet<Pattern>()
    private val offered = HashSet<Pair<Pattern, Pattern>>()
    private val missing = HashSet<Pattern>()
    val fullyCovered: Boolean get() = missing.isEmpty()

    fun offer(entry: Pattern, actual: Pattern) {
        ap.cancellation.checkpoint()
        if (!offered.add(entry to actual)) return
        val emitted = emit(entry, actual, ap.marks) ?: return
        if (keys.add(emitted)) initials += ap.initial(emitted)
        missing.remove(emitted)
    }
    fun has(entry: Pattern, actual: Pattern): Boolean {
        ap.cancellation.checkpoint()
        val emitted = emit(entry, actual, ap.marks) ?: return true
        return emitted in keys
    }
    fun requireFamily(target: Pattern, flow: Boolean, actual: Pattern) {
        fun require(entry: Pattern) {
            val potential = emit(entry, actual, ap.marks) ?: return
            if (potential !in keys) missing += potential
        }
        require(target)
        if (flow && actual.fact.mark is MarkSlot.Concrete && actual.fact.mark.mark != TaintMark.ZERO)
            require(target.copy(fact = target.fact.copy(mark = actual.fact.mark)))
    }
}
