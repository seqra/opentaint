package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import java.util.Collections
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId

/** Immutable demand snapshot. Tails, marks, exclusions and exits remain candidate payloads. */
class DemandStore private constructor(
    private val byMethod: Map<MethodKey, MethodDemandIndex>,
    private val controls: Map<MethodKey, List<PairedDemand>>,
    private val ap: ApManager,
    val hasSharedStaticCarry: Boolean,
    internal val completion: FrozenCompletion?,
    private val scoped: Map<OwnedScope, ScopedDemandIndex>,
    private val scopedCompletions: Map<OwnedScope, FrozenCompletion>,
) {
    private class MethodDemandIndex(val entries: PathTrie<Pattern>, val rows: List<DemandPattern>,
                                   val byEntry: PathTrie<Int>, val byExit: PathTrie<Int>, val entryCount: Int)
    private class ScopedDemandIndex(
        val data: MethodDemandIndex,
        val rowPorts: List<PortId>,
        val controls: List<Pair<PortId, PairedDemand>>,
    )
    private data class Query(val method: MethodKey, val scope: BlockScope? = null, val exit: PortId? = null)
    private fun local(query: Query): MethodDemandIndex? = query.scope?.let {
        scoped[OwnedScope(query.method, it)]?.data
    } ?: if (query.scope == null) byMethod[query.method] else null

    private fun completion(query: Query): FrozenCompletion? =
        if (query.scope == null) completion else scopedCompletions[OwnedScope(query.method, query.scope)]?.selectExit(query.exit)

    /** C2 borrows the union of this entry's exits; C5 selects one actual exit. */
    fun scope(method: MethodKey, scope: BlockScope): ScopeDemandView = object : PreparedScopeDemandView {
        override fun initials(actual: Facts, policy: RestrictedInitialPolicy): Set<AdmittedInitial> =
            initials(Query(method, scope), actual, policy)
        override fun intersect(exit: PortId, original: PremiseKey, raw: Facts,
                               policy: RestrictedInitialPolicy): List<Facts> =
            intersect(Query(method, scope, exit), original, raw, policy)
        override fun acceptsTarget(exit: PortId, original: PremiseKey, policy: RestrictedInitialPolicy): Boolean =
            intersect(Query(method, scope, exit), original, Reach.DEMAND, policy).isNotEmpty()
        override fun prepareDataPlan(exit: PortId, templates: List<Pattern>, policy: RestrictedInitialPolicy,
                                     onEntryCheck: () -> Unit): PreparedLocalDataPlan? =
            prepareLocalDataPlan(Query(method, scope, exit), templates, policy, onEntryCheck)
    }

    internal fun prepareDataPlan(method: MethodKey, templates: List<Pattern>,
                                 policy: RestrictedInitialPolicy, onEntryCheck: () -> Unit = {}): PreparedLocalDataPlan? =
        prepareLocalDataPlan(Query(method), templates, policy, onEntryCheck)

    /** Exact local DATA capability. Static/control/unsupported cases keep native C5. */
    private fun prepareLocalDataPlan(query: Query, templates: List<Pattern>,
                                     policy: RestrictedInitialPolicy, onEntryCheck: () -> Unit): PreparedLocalDataPlan? {
        ap.cancellation.checkpoint()
        if (policy.run < 3 || hasStaticCompletion || hasSharedStaticCarry || templates.isEmpty() || templates.size > 2048 ||
            templates.any { it.fact.base == AccessPathBase.Zero }) return null
        val local = local(query)
        val ops = ApOps(ap)
        data class Planned(val member: Int, val id: Int, val pair: DemandPattern, val ticket: EntryRestrictionTicket?)
        val rows = ArrayList<Planned>()
        for ((ordinal, member) in templates.withIndex()) {
            ap.cancellation.checkpoint()
            if (local != null) for (id in local.byEntry.lookupPrefixes(member.fact.base, member.fact.path.toIntArray())) {
                if (query.scope != null && query.exit != null &&
                    scoped.getValue(OwnedScope(query.method, query.scope)).rowPorts[id] != query.exit) continue
                if (rows.size + templates.size == 2048) return null
                val pair = local.rows[id]
                onEntryCheck()
                rows += Planned(ordinal, id, pair, EntryRestrictionTicket.prepare(ops, member, pair, policy))
            }
        }
        return object : PreparedLocalDataPlan {
            override val rowChecks: Int = rows.size
            override fun emptyForBase(base: AccessPathBase): Boolean = rows.none {
                it.ticket != null && it.pair.exit?.fact?.base == base
            }
            override fun intersect(original: PremiseKey, raw: Facts): List<Facts>? {
                ap.cancellation.checkpoint()
                if (raw is Reach || original.isZero || original.members.map { it.toPattern() } != templates) return null
                if (!RuntimeDataDomain.packet(original, raw)) return emptyList()
                val result = ExactDemandResults(ap)
                val outputIds = HashSet<Int>()
                if (local != null) for (leaf in ops.leaves(raw))
                    local.byExit.visitAround(leaf.fact.base, leaf.fact.path.toIntArray()) { outputIds += it }
                for (row in rows) {
                    ap.cancellation.checkpoint()
                    if (row.id !in outputIds) continue
                    statistics?.add(7)
                    if (row.pair.exit == null) continue
                    statistics?.add(9)
                    offerDataPair(query.method, ops, original.member(row.member), raw, row.pair, policy,
                        result, route = 0, prepared = true, ticket = row.ticket)
                }
                return result.all()
            }
        }
    }

    private val statistics = if (java.lang.Boolean.getBoolean("org.opentaint.bidi.optimizationStatistics"))
        DemandQueryStatistics() else null
    val hasStaticCompletion: Boolean get() = completion != null || scopedCompletions.isNotEmpty()
    internal fun validateIncoming(run: Int) {
        require(run >= 2)
        check(run == 2 || !hasStaticCompletion && !hasSharedStaticCarry) {
            "Only run-2 can use the run-1 static completion"
        }
        for (method in byMethod.values + scoped.values.map { it.data }) for (d in method.rows) {
            ap.cancellation.checkpoint()
            if (d.entry.fact.mark !is MarkSlot.Star) continue
            check(d.entry.fact.tail == Tail.ANY || run == 2 && d.entry.fact.tail == Tail.STAR) {
                "A run-$run FLOW demand entry must be ANY (STAR is valid only in run-2): $d"
            }
            check(d.exit == null || d.exit.fact.mark is MarkSlot.Star &&
                d.exit.fact.tail in setOf(Tail.STAR, Tail.ANY)) { "Invalid paired FLOW exit: $d" }
        }
        for (rows in controls.values + scoped.values.map { it.controls.map { row -> row.second } }) for (row in rows) {
            ap.cancellation.checkpoint()
            val entry = (row.entry as? DemandEntry.Data)?.pattern ?: continue
            if (entry.fact.mark is MarkSlot.Star)
                check(entry.fact.tail == Tail.ANY || run == 2 && entry.fact.tail == Tail.STAR) {
                    "A run-$run FLOW demand entry must be ANY (STAR is valid only in run-2): $row"
                }
        }
    }
    fun staticCompletionStatistics(): String? = (completion?.statistics() ?: "localOnly=${!hasStaticCompletion}") +
        " scopedCompletions=${scopedCompletions.size}" +
        " entryRows=${byMethod.values.sumOf { it.entryCount.toLong() } + scoped.values.sumOf { it.data.entryCount.toLong() }}" +
        " pairRows=${byMethod.values.sumOf { it.rows.size.toLong() } + controls.values.sumOf { it.size.toLong() } +
            scoped.values.sumOf { it.data.rows.size.toLong() + it.controls.size.toLong() }}" +
        (statistics?.let { " $it" } ?: "")
    internal fun diagnosticC5Samples(): List<String> = statistics?.rowSamples().orEmpty()

    /** C2 uses an entry-only index and never materializes origin products. */
    fun admissionPolicy(run: Int, fieldLimit: Int, direction: Direction): RestrictedInitialPolicy =
        RestrictedInitialPolicy(run, fieldLimit, direction, ap.marks)

    fun initials(method: MethodKey, boundedActual: Facts,
                 policy: RestrictedInitialPolicy = RestrictedInitialPolicy(direction = Direction.FORWARD, catalog = ap.marks)): Set<AdmittedInitial> {
        return initials(Query(method), boundedActual, policy)
    }

    private fun initials(query: Query, boundedActual: Facts, policy: RestrictedInitialPolicy): Set<AdmittedInitial> {
        val method = query.method
        ap.cancellation.checkpoint()
        statistics?.add(0)
        if (!RuntimeDataDomain.base(boundedActual.base)) return emptySet()
        if (boundedActual is Reach) {
            var admitted = false
            visitControlPairs(query, policy) { pair ->
                admitted = pair.entry == DemandEntry.Zero || pair.entry == DemandEntry.Target
                !admitted
            }
            return if (admitted) setOf(existingZeroAdmission(ap.zero)) else emptySet()
        }
        val ops = ApOps(ap)
        val leaves = ops.leaves(boundedActual).toList()
        val result = InitialDemandResults(ap, policy, boundedActual.layer, statistics)
        val local = local(query)
        for (leaf in leaves) {
            ap.cancellation.checkpoint()
            local?.entries?.visitAround(leaf.fact.base, leaf.fact.path.toIntArray()) { result.offer(it, leaf) }
            staticCarry(leaf)?.let { result.offer(it.entry, leaf) }
        }
        val skipped = completion(query) ?: return result.initials // run-3 onward: local only
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
        return intersect(Query(method), original, raw, policy)
    }

    private fun intersect(query: Query, original: PremiseKey, raw: Facts,
                          policy: RestrictedInitialPolicy): List<Facts> {
        val method = query.method
        ap.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(original, raw)) return emptyList()
        val ops = ApOps(ap)
        val result = ExactDemandResults(ap)
        // Reach has one possible result. DATA must exhaust rows with different exit budgets.
        fun saturated(): Boolean = raw is Reach && result.hasResults
        val local = local(query)
        val outputLeaves = ops.leaves(raw).toList()
        // A control pair is tested as one row. Entry and exit permissions cannot mix.
        visitControlPairs(query, policy, includeDerived = original.isZero) { pair ->
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
                if (id in outputIds && (query.scope == null || query.exit == null ||
                        scoped[OwnedScope(method, query.scope)]!!.rowPorts[id] == query.exit))
                    offer(member, local.rows[id])
            }
            staticCarry(member.toPattern())?.let { offer(member, it, route = 3) }
        }
        val skipped = completion(query) ?: return result.all() // later snapshots have no graph lookup
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
                              policy: RestrictedInitialPolicy, result: ExactDemandResults, route: Int,
                              prepared: Boolean = false, ticket: EntryRestrictionTicket? = null) {
        ap.cancellation.checkpoint()
        val exit = pair.exit ?: return
        val depth = exit.fact.path.count { it.isCounted() }
        val global = policy.fieldLimit
        check(global >= 1)
        // Clamp before adding: the default public policy uses Int.MAX_VALUE.
        val budget = if (depth >= global) global else depth + 1
        statistics?.dataRow(raw, exit, budget, route)
        val sampledRow = statistics?.sampleRow(method, member, raw, pair, budget, route)
        val selected = if (prepared) ticket?.restrict(raw).orEmpty() else ops.restrict(member, raw, pair, policy)
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

    /** A run-1 static write used the typed raw-write shortcut, not a
     * completed normal exit or physical loop leave. Its reverse W row therefore has STATIC_SHORTCUT as its
     * entry. An actually reached run-2 static initial can finish at a source
     * through that same shortcut, while its live DATA scope stays physical.
     * Only complete W/B paths with a genuine ZERO origin can admit Target;
     * shared carry, unrelated normal demand and terminal-reader rows cannot. */
    internal fun acceptsStaticShortcutTarget(method: MethodKey, block: BlockId, exit: PortId,
                                             original: PremiseKey, policy: RestrictedInitialPolicy): Boolean {
        if (policy.run != 2 || policy.direction != Direction.BACKWARD) return false
        val member = original as? InitialAp ?: return false
        if (member.base != STATIC || member.mark !is MarkSlot.Concrete) return false
        val owner = OwnedScope(method, BlockScope(block, PortId.STATIC_SHORTCUT))
        val skipped = scopedCompletions[owner]?.selectExit(exit) ?: return false
        val ops = ApOps(ap)
        val outputs = listOf(ap.zero.toPattern())
        var accepted = false
        fun offer(pair: DemandPattern) {
            ap.cancellation.checkpoint()
            if (pair.entry.fact.base != STATIC || pair.exit?.fact?.base != AccessPathBase.Zero) return
            if (ops.restrict(member, Reach.DEMAND, pair, policy).isNotEmpty()) accepted = true
        }
        for (row in skipped.local(method).pairs(member, outputs)) {
            ap.cancellation.checkpoint()
            offer(DemandPattern(row.to, row.from))
            if (accepted) return true
        }
        val query = StaticPairLookup(ap, skipped, statistics) { entry, initial ->
            policy.canStoreInitial(entry, initial.toPattern())
        }
        query.walk(method, member, outputs, visible = false,
            offer = { _, pair -> offer(pair) }, covered = { accepted })
        if (accepted) return true
        if (!skipped.mayNeedInheritedPairs(method)) return false
        query.walk(method, member, outputs, visible = true,
            offer = { _, pair -> offer(pair) }, covered = { accepted })
        return accepted
    }

    /** Virtual terminal pairs share the run-1 static graph; no closure rows are retained. */
    private fun visitControlPairs(query: Query, policy: RestrictedInitialPolicy, includeDerived: Boolean = true,
                                  visit: (PairedDemand) -> Boolean): Boolean {
        val method = query.method
        if (query.scope == null) {
            for (pair in controls[method].orEmpty()) {
                ap.cancellation.checkpoint()
                if (!visit(pair)) return false
            }
        } else for ((exit, pair) in scoped[OwnedScope(method, query.scope)]?.controls.orEmpty()) {
            ap.cancellation.checkpoint()
            if ((query.exit == null || query.exit == exit) && !visit(pair)) return false
        }
        val skipped = completion(query)?.takeIf { includeDerived } ?: return true
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
        private val scopedRows = LinkedHashSet<Pair<ScopedSummaryKey, DemandPattern>>()
        private val scopedControls = LinkedHashSet<Pair<ScopedSummaryKey, PairedDemand>>()
        private var staticCarry = false
        private var completion: FrozenCompletion? = null
        private val scopedCompletions = LinkedHashMap<OwnedScope, FrozenCompletion>()

        /** Only the completed run-1 boundary installs these virtual guidance families. */
        fun withCompletion(view: FrozenCompletion) { completion = view }
        fun withCompletion(method: MethodKey, scope: BlockScope, view: FrozenCompletion) {
            scopedCompletions[OwnedScope(method, scope)] = view
        }
        fun withSharedStaticCarry() { staticCarry = true }

        /** Count only a new exact normalized pattern. Validate the typed hand-off boundary. */
        fun add(method: MethodKey, d: DemandPattern): Boolean = add(method, null, d)

        fun add(method: MethodKey, scope: BlockScope, exit: PortId, d: DemandPattern): Boolean =
            add(method, ScopedSummaryKey(method, scope, exit), d)

        private fun add(method: MethodKey, key: ScopedSummaryKey?, d: DemandPattern): Boolean {
            m.cancellation.checkpoint()
            if (!RuntimeDataDomain.base(d.entry.fact.base) ||
                d.exit?.let { !RuntimeDataDomain.base(it.fact.base) } == true) return false
            if (d.entry.fact.base == AccessPathBase.Zero || d.exit?.fact?.base == AccessPathBase.Zero) {
                val exit = d.exit ?: return false // No unpaired implicit ZERO permission.
                return add(method, key, PairedDemand(
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
            return if (key == null) seen.add(method to owned) else scopedRows.add(key to owned)
        }

        /** Data pairs keep the current AP index; control rows use only this local list. */
        fun add(method: MethodKey, row: PairedDemand): Boolean = add(method, null, row)

        fun add(method: MethodKey, scope: BlockScope, exit: PortId, row: PairedDemand): Boolean =
            add(method, ScopedSummaryKey(method, scope, exit), row)

        private fun add(method: MethodKey, key: ScopedSummaryKey?, row: PairedDemand): Boolean {
            m.cancellation.checkpoint()
            if (row.entry is DemandEntry.Data && !RuntimeDataDomain.base(row.entry.pattern.fact.base) ||
                row.exit is DemandExit.Data && !RuntimeDataDomain.base(row.exit.pattern.fact.base)) return false
            if (row.entry is DemandEntry.Data && row.exit is DemandExit.Data)
                return add(method, key, DemandPattern(row.entry.pattern, row.exit.pattern))
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
            val owned = PairedDemand(entry, exit)
            return if (key == null) controlRows.add(method to owned) else scopedControls.add(key to owned)
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
                byMethod[method] = index(rows, controls[method].orEmpty())
            }
            val scopeData = LinkedHashMap<OwnedScope, MutableList<Pair<PortId, DemandPattern>>>()
            val scopeControls = LinkedHashMap<OwnedScope, MutableList<Pair<PortId, PairedDemand>>>()
            for ((key, row) in scopedRows) {
                m.cancellation.checkpoint()
                scopeData.getOrPut(OwnedScope(key.method, key.scope)) { ArrayList() } += key.exit to row
            }
            for ((key, row) in scopedControls) {
                m.cancellation.checkpoint()
                val owner = OwnedScope(key.method, key.scope)
                scopeControls.getOrPut(owner) { ArrayList() } += key.exit to row
                scopeData.getOrPut(owner) { ArrayList() }
            }
            val scopes = LinkedHashMap<OwnedScope, ScopedDemandIndex>()
            for ((owner, rows) in scopeData) {
                m.cancellation.checkpoint()
                val control = scopeControls[owner].orEmpty()
                scopes[owner] = ScopedDemandIndex(index(rows.map { it.second }, control.map { it.second }),
                    Collections.unmodifiableList(rows.map { it.first }), Collections.unmodifiableList(control.toList()))
            }
            return DemandStore(Collections.unmodifiableMap(byMethod),
                Collections.unmodifiableMap(controls.mapValues { Collections.unmodifiableList(it.value) }),
                m, staticCarry, completion, Collections.unmodifiableMap(scopes),
                Collections.unmodifiableMap(LinkedHashMap(scopedCompletions)))
        }

        private fun index(rows: List<DemandPattern>, controls: List<PairedDemand>): MethodDemandIndex {
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
            for (row in controls) {
                m.cancellation.checkpoint()
                val entry = (row.entry as? DemandEntry.Data)?.pattern ?: continue
                if (entries.add(entry.fact.base, entry.fact.path.toIntArray(), entry)) entryCount++
            }
            return MethodDemandIndex(entries, Collections.unmodifiableList(rows.toList()), byEntry, byExit, entryCount)
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


/** Read-only view bound to one method-owned block entry. C5 additionally names
 * the actual output port, so permissions from separate exits cannot mix. */
interface ScopeDemandView {
    fun initials(actual: Facts, policy: RestrictedInitialPolicy): Set<AdmittedInitial>
    fun intersect(exit: PortId, original: PremiseKey, raw: Facts,
                  policy: RestrictedInitialPolicy): List<Facts>
    fun acceptsTarget(exit: PortId, original: PremiseKey, policy: RestrictedInitialPolicy): Boolean
}
