package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import java.util.Collections

/** Immutable demand snapshot. Tails, marks, exclusions and exits remain candidate payloads. */
class DemandStore private constructor(
    private val byMethod: Map<MethodKey, MethodDemandIndex>,
    internal val zeroDemand: DemandPattern,
    private val ap: ApManager,
    val hasSharedStaticCarry: Boolean,
    internal val completion: FrozenCompletion?,
) {
    private class MethodDemandIndex(val entries: PathTrie<Pattern>, val rows: List<DemandPattern>,
                                   val byEntry: PathTrie<Int>, val byExit: PathTrie<Int>, val entryCount: Int)
    private val statistics = if (java.lang.Boolean.getBoolean("org.opentaint.bidi.optimizationStatistics"))
        DemandQueryStatistics() else null
    val hasStaticCompletion: Boolean get() = completion != null
    fun staticCompletionStatistics(): String? = (completion?.statistics() ?: "localOnly=true") +
        " entryRows=${byMethod.values.sumOf { it.entryCount.toLong() }}" +
        " pairRows=${byMethod.values.sumOf { it.rows.size.toLong() }}" +
        (statistics?.let { " $it" } ?: "")

    /** C2 uses an entry-only index and never materializes origin products. */
    fun initials(method: MethodKey, boundedActual: Facts): Set<InitialAp> {
        ap.cancellation.checkpoint()
        statistics?.add(0)
        val ops = ApOps(ap)
        val leaves = ops.leaves(boundedActual).toList()
        val result = InitialDemandResults(ap)
        val local = byMethod[method]
        for (leaf in leaves) {
            ap.cancellation.checkpoint()
            local?.entries?.visitAround(leaf.fact.base, leaf.fact.path.toIntArray()) { result.offer(it, leaf) }
            if (leaf.fact.base == AccessPathBase.Zero) result.offer(zeroDemand.entry, leaf)
            staticCarry(leaf)?.let { result.offer(it.entry, leaf) }
        }
        val skipped = completion ?: return result.initials // run-3 onward: local only
        val query = StaticEntryLookup(ap, method, skipped, leaves, result, statistics)
        query.directLocal()
        // This query-local structural bound uses scalar emit only. No possible key is interned.
        for (leaf in leaves) {
            ap.cancellation.checkpoint()
            local?.entries?.visitAround(leaf.fact.base, leaf.fact.path.toIntArray()) {
                result.requireFamily(it, false, leaf)
            }
            skipped.visitPossibleTargets(method, leaf) { target, flow ->
                result.requireFamily(target, flow, leaf); true
            }
        }
        fun covered(): Boolean = result.fullyCovered
        if (covered()) { statistics?.add(3); return result.initials }
        query.search(visible = false, ::covered)
        if (covered()) { statistics?.add(3); return result.initials }
        if (!skipped.mayNeedInheritedEntries(method, leaves)) return result.initials
        query.search(visible = true, ::covered)
        return result.initials
    }

    /** C5 selects complete paired rows and preserves the whole original ND premise at the caller. */
    fun intersect(method: MethodKey, original: PremiseKey, raw: Facts): List<Facts> {
        ap.cancellation.checkpoint()
        val ops = ApOps(ap)
        val result = ExactDemandResults(ap, ops)
        val local = byMethod[method]
        val outputLeaves = ops.leaves(raw).toList()
        fun offer(member: InitialAp, pair: DemandPattern) {
            statistics?.add(7)
            if (pair.exit == null) return
            statistics?.add(9)
            for (kept in ops.restrict(member, raw, pair)) result.add(kept)
        }
        val outputIds = HashSet<Int>()
        if (local != null) for (leaf in outputLeaves)
            local.byExit.visitAround(leaf.fact.base, leaf.fact.path.toIntArray()) { outputIds += it }
        original.forEachMember { member ->
            ap.cancellation.checkpoint()
            if (local != null) for (id in local.byEntry.lookupPrefixes(member.base,
                    member.path?.toIntArray() ?: EMPTY_PATH)) {
                if (id in outputIds) offer(member, local.rows[id])
            }
            staticCarry(member.toPattern())?.let { offer(member, it) }
        }
        val skipped = completion ?: return result.all() // later snapshots have no graph lookup
        // Primitive seed pairs use the same complete source/target row. They do not form a product.
        val primitive = skipped.local(method)
        original.forEachMember { member ->
            for (edge in primitive.pairs(member, outputLeaves))
                offer(member, DemandPattern(edge.to, edge.from))
        }
        if (result.covers(raw)) { statistics?.add(10); return result.all() }
        val query = StaticPairLookup(ap, skipped, statistics)
        query.walk(method, original, outputLeaves, visible = false, ::offer) { result.covers(raw) }
        if (result.covers(raw)) { statistics?.add(10); return result.all() }
        if (!skipped.mayNeedInheritedPairs(method)) return result.all()
        query.walk(method, original, outputLeaves, visible = true, ::offer) { result.covers(raw) }
        return result.all()
    }

    /** Immutable seed inspection for the finite explicit reference in tests. No closure is retained. */
    internal fun explicitRows(method: MethodKey): List<DemandPattern> {
        ap.cancellation.checkpoint()
        return byMethod[method]?.rows.orEmpty()
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
            val grouped = LinkedHashMap<MethodKey, MutableList<DemandPattern>>()
            for ((method, demand) in seen) {
                m.cancellation.checkpoint()
                grouped.getOrPut(method) { ArrayList() } += demand
            }
            val byMethod = LinkedHashMap<MethodKey, MethodDemandIndex>()
            for ((method, rows) in grouped) {
                val entries = PathTrie<Pattern>(m.cancellation)
                val byEntry = PathTrie<Int>(m.cancellation)
                val byExit = PathTrie<Int>(m.cancellation)
                var entryCount = 0
                for ((id, demand) in rows.withIndex()) {
                    m.cancellation.checkpoint()
                    if (entries.add(demand.entry.fact.base, demand.entry.fact.path.toIntArray(), demand.entry)) entryCount++
                    byEntry.add(demand.entry.fact.base, demand.entry.fact.path.toIntArray(), id)
                    demand.exit?.let { byExit.add(it.fact.base, it.fact.path.toIntArray(), id) }
                }
                byMethod[method] = MethodDemandIndex(entries, Collections.unmodifiableList(rows), byEntry, byExit, entryCount)
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
