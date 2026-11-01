package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import java.util.Collections

/** Immutable demand snapshot. Tails, marks, exclusions and exits remain candidate payloads. */
class DemandStore private constructor(
    private val byMethod: Map<MethodKey, MethodDemandIndex>,
    private val controls: Map<MethodKey, List<PairedDemand>>,
    private val ap: ApManager,
    val hasSharedStaticCarry: Boolean,
    internal val completion: FrozenCompletion?,
) {
    private class MethodDemandIndex(val entries: PathTrie<Pattern>, val rows: List<DemandPattern>,
                                   val byEntry: PathTrie<Int>, val byExit: PathTrie<Int>, val entryCount: Int)
    private val statistics = if (java.lang.Boolean.getBoolean("org.opentaint.bidi.optimizationStatistics"))
        DemandQueryStatistics() else null
    val hasStaticCompletion: Boolean get() = completion != null
    internal fun validateIncoming(run: Int) {
        require(run >= 2)
        check(run == 2 || completion == null && !hasSharedStaticCarry) {
            "Only run-2 can use the run-1 static completion"
        }
        for (method in byMethod.values) for (d in method.rows) {
            ap.cancellation.checkpoint()
            if (d.entry.fact.mark !is MarkSlot.Star) continue
            check(d.entry.fact.tail == Tail.ANY || run == 2 && d.entry.fact.tail == Tail.STAR) {
                "A run-$run FLOW demand entry must be ANY (STAR is valid only in run-2): $d"
            }
            check(d.exit == null || d.exit.fact.mark is MarkSlot.Star &&
                d.exit.fact.tail in setOf(Tail.STAR, Tail.ANY)) { "Invalid paired FLOW exit: $d" }
        }
        for (rows in controls.values) for (row in rows) {
            ap.cancellation.checkpoint()
            val entry = (row.entry as? DemandEntry.Data)?.pattern ?: continue
            if (entry.fact.mark is MarkSlot.Star)
                check(entry.fact.tail == Tail.ANY || run == 2 && entry.fact.tail == Tail.STAR) {
                    "A run-$run FLOW demand entry must be ANY (STAR is valid only in run-2): $row"
                }
        }
    }
    fun staticCompletionStatistics(): String? = (completion?.statistics() ?: "localOnly=true") +
        " entryRows=${byMethod.values.sumOf { it.entryCount.toLong() }}" +
        " pairRows=${byMethod.values.sumOf { it.rows.size.toLong() } + controls.values.sumOf { it.size.toLong() }}" +
        (statistics?.let { " $it" } ?: "")
    internal fun diagnosticC5Samples(): List<String> = statistics?.rowSamples().orEmpty()

    /** C2 uses an entry-only index and never materializes origin products. */
    fun admissionPolicy(run: Int, fieldLimit: Int, direction: Direction): RestrictedInitialPolicy =
        RestrictedInitialPolicy(run, fieldLimit, direction, ap.marks)

    fun initials(method: MethodKey, boundedActual: Facts,
                 policy: RestrictedInitialPolicy = RestrictedInitialPolicy(direction = Direction.FORWARD, catalog = ap.marks)): Set<AdmittedInitial> {
        ap.cancellation.checkpoint()
        statistics?.add(0)
        if (!RuntimeDataDomain.base(boundedActual.base)) return emptySet()
        if (boundedActual is Reach) {
            var admitted = false
            visitControlPairs(method, policy) { pair ->
                admitted = pair.entry == DemandEntry.Zero || pair.entry == DemandEntry.Target
                !admitted
            }
            return if (admitted) setOf(existingZeroAdmission(ap.zero)) else emptySet()
        }
        val ops = ApOps(ap)
        val leaves = ops.leaves(boundedActual).toList()
        val result = InitialDemandResults(ap, policy, boundedActual.layer, statistics)
        val local = byMethod[method]
        for (leaf in leaves) {
            ap.cancellation.checkpoint()
            local?.entries?.visitAround(leaf.fact.base, leaf.fact.path.toIntArray()) { result.offer(it, leaf) }
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
    fun intersect(method: MethodKey, original: PremiseKey, raw: Facts,
                  policy: RestrictedInitialPolicy = RestrictedInitialPolicy(direction = Direction.FORWARD, catalog = ap.marks)): List<Facts> {
        ap.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(original, raw)) return emptyList()
        val ops = ApOps(ap)
        val result = ExactDemandResults(ap)
        // Reach has one possible result. DATA must exhaust rows with different exit budgets.
        fun saturated(): Boolean = raw is Reach && result.hasResults
        val local = byMethod[method]
        val outputLeaves = ops.leaves(raw).toList()
        // A control pair is tested as one row. Entry and exit permissions cannot mix.
        visitControlPairs(method, policy, includeDerived = original.isZero) { pair ->
            ap.cancellation.checkpoint()
            if (!entryAccepts(pair.entry, original, policy)) return@visitControlPairs true
            when (val exit = pair.exit) {
                DemandExit.Zero -> if (raw is Reach) result.add(raw)
                is DemandExit.Data -> if (raw !is Reach) {
                    // Data/Data rows use the AP index. A control entry admitted ZERO;
                    // use the existing AP restriction, including protection transport.
                    val dataPair = DemandPattern(ap.zero.toPattern(), exit.pattern)
                    offerDataPair(method, ops, ap.zero, raw, dataPair, policy, result, route = 2)
                }
            }
            !saturated()
        }
        fun offer(member: InitialAp, pair: DemandPattern, route: Int = 0) {
            statistics?.add(7)
            val exit = pair.exit ?: return
            statistics?.add(9)
            if (exit.fact.base == AccessPathBase.Zero) {
                // The static walker can expose a typed ZERO through its legacy AP view.
                if (raw is Reach) for (kept in ops.restrict(member, raw, pair, policy)) result.add(kept)
            } else offerDataPair(method, ops, member, raw, pair, policy, result, route)
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
            staticCarry(member.toPattern())?.let { offer(member, it, route = 3) }
        }
        val skipped = completion ?: return result.all() // later snapshots have no graph lookup
        // Primitive seed pairs use the same complete source/target row. They do not form a product.
        val primitive = skipped.local(method)
        original.forEachMember { member ->
            for (edge in primitive.pairs(member, outputLeaves))
                offer(member, DemandPattern(edge.to, edge.from), route = 1)
        }
        if (saturated()) { statistics?.add(10); return result.all() }
        val query = StaticPairLookup(ap, skipped, statistics) { entry, member -> policy.canStoreInitial(entry, member.toPattern()) }
        val offerVirtual: (InitialAp, DemandPattern) -> Unit = { member, pair -> offer(member, pair, route = 1) }
        query.walk(method, original, outputLeaves, visible = false, offerVirtual, ::saturated)
        if (saturated()) { statistics?.add(10); return result.all() }
        if (!skipped.mayNeedInheritedPairs(method)) return result.all()
        query.walk(method, original, outputLeaves, visible = true, offerVirtual, ::saturated)
        return result.all()
    }

    /** Exact C5 must precede the cut, and each complete row supplies its own exit depth. */
    private fun offerDataPair(method: MethodKey, ops: ApOps, member: InitialAp, raw: Facts, pair: DemandPattern,
                              policy: RestrictedInitialPolicy, result: ExactDemandResults, route: Int) {
        ap.cancellation.checkpoint()
        val exit = pair.exit ?: return
        val depth = exit.fact.path.count { it.isCounted() }
        val global = policy.fieldLimit
        check(global >= 1)
        // Clamp before adding: the default public policy uses Int.MAX_VALUE.
        val budget = if (depth >= global) global else depth + 1
        statistics?.dataRow(raw, exit, budget, route)
        val sampledRow = statistics?.sampleRow(method, member, raw, pair, budget, route)
        val selected = ops.restrict(member, raw, pair, policy)
        if (selected.isEmpty()) {
            statistics?.rejectedRow()
            statistics?.sampleResult(sampledRow, null, null)
        }
        for (kept in selected) {
            statistics?.selected(kept, budget)
            ops.limit(kept, budget, object : ApOut {
                override fun result(f: Facts) {
                    statistics?.limited(kept, f)
                    statistics?.sampleResult(sampledRow, kept, f)
                    result.add(f)
                }
                override fun markRequest(mark: TaintMark) = error("A field cut must not emit a mark request")
            })
        }
    }

    /** Immutable seed inspection for the finite explicit reference in tests. No closure is retained. */
    internal fun explicitRows(method: MethodKey): List<DemandPattern> {
        ap.cancellation.checkpoint()
        val ordinary = byMethod[method]?.rows.orEmpty()
        return ordinary + controls[method].orEmpty().mapNotNull { row ->
            val entry = when (val e = row.entry) {
                is DemandEntry.Data -> e.pattern
                DemandEntry.Zero -> ap.zero.toPattern()
                DemandEntry.Target -> return@mapNotNull null
            }
            val exit = when (val e = row.exit) {
                is DemandExit.Data -> e.pattern
                DemandExit.Zero -> ap.zero.toPattern()
            }
            DemandPattern(entry, exit)
        }
    }

    /** Terminal C5 needs one complete pair with a ZERO exit, explicit or run-2 static-composed. */
    fun acceptsTarget(method: MethodKey, original: PremiseKey,
                      policy: RestrictedInitialPolicy = RestrictedInitialPolicy(direction = Direction.FORWARD, catalog = ap.marks)): Boolean {
        // ZERO and Target match exactly the same exit slots. This read-only probe
        // reuses all paired C5 lookup paths; it never stores or propagates a ZERO edge.
        return intersect(method, original, Reach.DEMAND, policy).isNotEmpty()
    }

    /** Virtual terminal pairs share the run-1 static graph; no closure rows are retained. */
    private fun visitControlPairs(method: MethodKey, policy: RestrictedInitialPolicy, includeDerived: Boolean = true,
                                  visit: (PairedDemand) -> Boolean): Boolean {
        for (pair in controls[method].orEmpty()) {
            ap.cancellation.checkpoint()
            if (!visit(pair)) return false
        }
        val skipped = completion?.takeIf { includeDerived } ?: return true
        val query = StaticPairLookup(ap, skipped, statistics) { entry, member ->
            policy.canStoreInitial(entry, member.toPattern())
        }
        fun walk(visible: Boolean): Boolean = query.walkTargetOrigins(method, visible) { origin ->
            val exit = if (origin.fact.base == AccessPathBase.Zero) DemandExit.Zero else DemandExit.Data(origin)
            visit(PairedDemand(DemandEntry.Target, exit))
        }
        if (!walk(false)) return false
        return !skipped.mayNeedInheritedPairs(method) || walk(true)
    }

    private fun entryAccepts(entry: DemandEntry, original: PremiseKey, policy: RestrictedInitialPolicy): Boolean {
        original.forEachMember { if (entryAccepts(entry, it, policy)) return true }
        return false
    }

    private fun entryAccepts(entry: DemandEntry, member: InitialAp, policy: RestrictedInitialPolicy): Boolean =
        when (entry) {
            DemandEntry.Zero, DemandEntry.Target -> member.isZero
            is DemandEntry.Data -> !member.isZero && policy.canStoreInitial(entry.pattern, member.toPattern())
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
        private val controlRows = LinkedHashSet<Pair<MethodKey, PairedDemand>>()
        private var staticCarry = false
        private var completion: FrozenCompletion? = null

        /** Only the completed run-1 boundary installs these virtual guidance families. */
        fun withCompletion(view: FrozenCompletion) { completion = view }
        fun withSharedStaticCarry() { staticCarry = true }

        /** Count only a new exact normalized pattern. Validate the typed hand-off boundary. */
        fun add(method: MethodKey, d: DemandPattern): Boolean {
            m.cancellation.checkpoint()
            if (!RuntimeDataDomain.base(d.entry.fact.base) ||
                d.exit?.let { !RuntimeDataDomain.base(it.fact.base) } == true) return false
            if (d.entry.fact.base == AccessPathBase.Zero || d.exit?.fact?.base == AccessPathBase.Zero) {
                val exit = d.exit ?: return false // No unpaired implicit ZERO permission.
                return add(method, PairedDemand(
                    if (d.entry.fact.base == AccessPathBase.Zero) DemandEntry.Zero else DemandEntry.Data(d.entry),
                    if (exit.fact.base == AccessPathBase.Zero) DemandExit.Zero else DemandExit.Data(exit),
                ))
            }
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
            return seen.add(method to owned)
        }

        /** Data pairs keep the current AP index; control rows use only this local list. */
        fun add(method: MethodKey, row: PairedDemand): Boolean {
            m.cancellation.checkpoint()
            if (row.entry is DemandEntry.Data && !RuntimeDataDomain.base(row.entry.pattern.fact.base) ||
                row.exit is DemandExit.Data && !RuntimeDataDomain.base(row.exit.pattern.fact.base)) return false
            if (row.entry is DemandEntry.Data && row.exit is DemandExit.Data)
                return add(method, DemandPattern(row.entry.pattern, row.exit.pattern))
            fun ownData(p: Pattern): Pattern {
                val normalized = normalizeDemandFieldExclusion(p)
                check(normalized.fact.base != AccessPathBase.Zero) { "Use a typed ZERO control endpoint" }
                check(normalized.fact.base !is AccessPathBase.CleanerTemporary)
                check(normalized.fact.tail != Tail.ANY_TAINT && normalizedMarks(normalized))
                check(validFieldExclusion(normalized))
                return ownPattern(m, normalized)
            }
            val entry = when (val e = row.entry) {
                is DemandEntry.Data -> DemandEntry.Data(ownData(e.pattern).also {
                    check(it.fact.mark !is MarkSlot.Star || it.fact.tail in setOf(Tail.ANY, Tail.STAR))
                })
                else -> e
            }
            val exit = when (val e = row.exit) {
                is DemandExit.Data -> DemandExit.Data(ownData(e.pattern))
                DemandExit.Zero -> DemandExit.Zero
            }
            return controlRows.add(method to PairedDemand(entry, exit))
        }

        /** The new index has no mutable alias in this builder or in earlier snapshots. */
        fun build(): DemandStore {
            m.cancellation.checkpoint()
            val grouped = LinkedHashMap<MethodKey, MutableList<DemandPattern>>()
            for ((method, demand) in seen) {
                m.cancellation.checkpoint()
                grouped.getOrPut(method) { ArrayList() } += demand
            }
            val controls = LinkedHashMap<MethodKey, MutableList<PairedDemand>>()
            for ((method, row) in controlRows) {
                controls.getOrPut(method) { ArrayList() } += row
                grouped.getOrPut(method) { ArrayList() }
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
                for (row in controls[method].orEmpty()) {
                    val entry = (row.entry as? DemandEntry.Data)?.pattern ?: continue
                    if (entries.add(entry.fact.base, entry.fact.path.toIntArray(), entry)) entryCount++
                }
                byMethod[method] = MethodDemandIndex(entries, Collections.unmodifiableList(rows), byEntry, byExit, entryCount)
            }
            return DemandStore(Collections.unmodifiableMap(byMethod),
                Collections.unmodifiableMap(controls.mapValues { Collections.unmodifiableList(it.value) }),
                m, staticCarry, completion)
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
