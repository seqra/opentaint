package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import java.util.Collections

/** Immutable demand snapshot. Tails, marks, exclusions and exits remain candidate payloads. */
class DemandStore private constructor(
    private val byMethod: Map<MethodKey, PathTrie<DemandPattern>>,
    private val zeroDemand: DemandPattern,
    private val ap: ApManager,
    val hasSharedStaticCarry: Boolean,
    private val completion: FrozenCompletion?,
) {
    val hasStaticCompletion: Boolean get() = completion != null
    fun staticCompletionStatistics(): String? = completion?.statistics()

    /** Emission tests prefixes and extensions, with the implicit zero demand on the zero base. */
    fun near(method: MethodKey, actual: Pattern): List<DemandPattern> {
        ap.cancellation.checkpoint()
        val stored = byMethod[method]?.around(actual.fact.base, actual.fact.path.toIntArray()).orEmpty()
        val completed = completion?.near(method, actual)?.toList().orEmpty()
        return when (actual.fact.base) {
            AccessPathBase.Zero -> stored + completed + zeroDemand
            STATIC -> staticCarry(actual)?.let { stored + completed + it } ?: (stored + completed)
            else -> stored + completed
        }.distinct()
    }

    /** Whole-premise restriction needs entry prefixes only. The implicit zero has no exit. */
    fun covering(method: MethodKey, initial: InitialAp): List<DemandPattern> {
        ap.cancellation.checkpoint()
        val stored = byMethod[method]?.lookupPrefixes(initial.base, initial.path?.toIntArray() ?: EMPTY_PATH).orEmpty()
        val completed = completion?.covering(method, initial)?.toList().orEmpty()
        return (staticCarry(initial.toPattern())?.let { stored + completed + it } ?: (stored + completed)).distinct()
    }

    /** Same actual slot and mark only. This family does not connect different fields. */
    private fun staticCarry(actual: Pattern): DemandPattern? {
        ap.cancellation.checkpoint()
        if (!hasSharedStaticCarry || actual.fact.base != STATIC) return null
        val pattern = guidancePattern(actual)
        return DemandPattern(pattern, pattern)
    }

    class Builder(private val m: ApManager) {
        private val seen = LinkedHashSet<Pair<MethodKey, DemandPattern>>()
        private val zeroDemand = ownDemand(m, DemandPattern(m.zero.toPattern(), null))
        private var staticCarry = false
        private var completion: FrozenCompletion? = null

        /** Only the completed run-1 boundary installs these virtual guidance families. */
        fun withCompletion(view: FrozenCompletion) { completion = view }
        fun withSharedStaticCarry() { staticCarry = true }

        /** Count only a new exact normalized pattern. Validate the typed hand-off boundary. */
        fun add(method: MethodKey, d: DemandPattern): Boolean {
            m.cancellation.checkpoint()
            val entry = normalizeDemandFieldExclusion(d.entry)
            val exit = d.exit?.let(::normalizeDemandFieldExclusion)
            check(entry.fact.base !is AccessPathBase.CleanerTemporary && exit?.fact?.base !is AccessPathBase.CleanerTemporary) {
                "A field-action temporary cannot enter a demand hand-off"
            }
            check(entry.fact.tail != Tail.ANY_TAINT && exit?.fact?.tail != Tail.ANY_TAINT) {
                "W8 (d): a demand pattern cannot have a must tail"
            }
            check(normalizedMarks(entry) && (exit == null || normalizedMarks(exit))) {
                "Normalize mark exclusions at hand-off"
            }
            check(entry.fact.mark !is MarkSlot.Star || entry.fact.tail == Tail.ANY || entry.fact.tail == Tail.STAR) {
                "A typed abstract demand entry has ANY or STAR tail"
            }
            check(exit?.fact?.tail != Tail.EXACT || entry.fact.mark is MarkSlot.Concrete) {
                "A canonical exact exit demand has a concrete entry mark"
            }
            check(validFieldExclusion(entry) && (exit == null || validFieldExclusion(exit))) {
                "Only STAR demand endpoints can exclude fields"
            }
            val owned = ownDemand(m, DemandPattern(entry, exit))
            return owned != zeroDemand && seen.add(method to owned)
        }

        /** The new index has no mutable alias in this builder or in earlier snapshots. */
        fun build(): DemandStore {
            m.cancellation.checkpoint()
            val byMethod = LinkedHashMap<MethodKey, PathTrie<DemandPattern>>()
            for ((method, demand) in seen) {
                m.cancellation.checkpoint()
                byMethod.getOrPut(method) { PathTrie(m.cancellation) }
                    .add(demand.entry.fact.base, demand.entry.fact.path.toIntArray(), demand)
            }
            return DemandStore(Collections.unmodifiableMap(byMethod), zeroDemand, m, staticCarry, completion)
        }
    }
}

private fun normalizedMarks(p: Pattern): Boolean =
    (p.fact.mark as? MarkSlot.Star)?.excluded?.isEmpty != false

private fun validFieldExclusion(p: Pattern): Boolean =
    p.exclusion == ExclusionSet.Empty || p.fact.tail == Tail.STAR

private fun ownDemand(m: ApManager, d: DemandPattern): DemandPattern =
    DemandPattern(ownPattern(m, d.entry), d.exit?.let { ownPattern(m, it) })

private fun ownPattern(m: ApManager, p: Pattern): Pattern {
    m.cancellation.checkpoint()
    val path = ArrayList<Int>(p.fact.path.size)
    for (accessor in p.fact.path) {
        m.cancellation.checkpoint()
        path += accessor
    }
    return p.copy(fact = p.fact.copy(path = Collections.unmodifiableList(path)))
}
