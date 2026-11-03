package org.opentaint.dataflow.bidi.store.reference

import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.ints.IntLinkedOpenHashSet
import it.unimi.dsi.fastutil.longs.Long2IntOpenHashMap
import it.unimi.dsi.fastutil.longs.Long2ObjectLinkedOpenHashMap
import it.unimi.dsi.fastutil.longs.LongArrayList
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.graph.PortId
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.CommonMethod
import java.util.Collections
import java.util.concurrent.atomic.AtomicLongArray


import org.opentaint.dataflow.bidi.store.*

/** Immutable pre-packing native oracle, copied from c7ed16e99c599ca926812c067df0b6608b6185f2. */
/** A geometry key has no runtime mark. Raw EXACT/FLOW patterns here are metadata only. */
private data class GuidanceGeometry(val from: Pattern, val to: Pattern) {
    fun edge(label: Long): StaticGuidanceEdge = edge(unpackBridgeMarks(label))
    fun edge(marks: GuidanceMarks): StaticGuidanceEdge = when (marks) {
        GuidanceMarks.Flow -> StaticGuidanceEdge(from, to, marks)
        is GuidanceMarks.Mapped -> StaticGuidanceEdge(
            from.copy(fact = from.fact.copy(mark = MarkSlot.Concrete(checkNotNull(marks.input)))),
            to.copy(fact = to.fact.copy(mark = MarkSlot.Concrete(checkNotNull(marks.output)))), marks)
    }
    companion object {
        fun of(edge: StaticGuidanceEdge) = GuidanceGeometry(
            edge.from.copy(fact = edge.from.fact.copy(mark = MarkSlot.STAR)),
            edge.to.copy(fact = edge.to.fact.copy(mark = MarkSlot.STAR)))
    }
}

/** B endpoints are static, so zero words are private sentinels, never runtime mark IDs. */
private fun packBridgeMarks(marks: GuidanceMarks): Long = when (marks) {
    GuidanceMarks.Flow -> 0L
    is GuidanceMarks.Mapped -> {
        val input = checkNotNull(marks.input).id.toLong() + 1L
        val output = checkNotNull(marks.output).id.toLong() + 1L
        (input shl 32) or (output and 0xffffffffL)
    }
}
private fun unpackBridgeMarks(label: Long): GuidanceMarks = if (label == 0L) GuidanceMarks.Flow else
    GuidanceMarks.Mapped(TaintMark((label ushr 32).toInt() - 1), TaintMark(label.toInt() - 1))

/** Incoming run-2 graph. B keys are shared; W/R remain attached to their complete MethodKey. */
class ReferenceFrozenStaticCompletion private constructor(
    private val ap: ApManager,
    private val graph: DetachedStaticCallGraph,
    private val bridges: List<BridgeRows>,
    private val bridgeEnds: PathTrie<Int>,
    private val bridgeStarts: PathTrie<Int>,
    private val flowStarts: PathTrie<Int>,
    private val flowEnds: PathTrie<Int>,
    private val coloredBridgeOutputs: SelectorRows,
    private val bridgeOwners: Set<CommonMethod>,
    private val ownBridges: Map<CommonMethod, LongArray>,
    private val bridgeEntryRows: List<EntryRows>,
    private val bridgeEntries: EntryDirectory,
    private val locals: Map<MethodKey, Attachments>,
    private val terminalReaders: Map<MethodKey, List<Pattern>>,
    private val scopedLocals: Map<ScopedSummaryKey, Attachments>,
    private val scopedTerminals: Map<ScopedSummaryKey, List<Pattern>>,
    private val scopedPorts: Set<ScopedSummaryKey>,
    private val ownerVisibility: FrozenOwnerVisibility,
    val seedMemberships: Long,
    val writerAttachments: Long,
    val readerAttachments: Long,
) : FrozenCompletion {
    // Opt-in query totals only. The immutable graph relation is shared by all views.
    private val ownerStatistics = if (java.lang.Boolean.getBoolean("org.opentaint.bidi.optimizationStatistics"))
        AtomicLongArray(4) else null
    val seedKeys: Int get() = bridges.sumOf { it.labels.size }
    val seedGeometries: Int get() = bridges.size
    override fun statistics(): String = "seedKeys=$seedKeys seedEntryKeys=${bridgeEntryRows.size} seedGeometries=$seedGeometries ownerMemberships=$seedMemberships " +
        "writerAttachments=$writerAttachments readerAttachments=$readerAttachments " +
        "terminalAttachments=${terminalReaders.values.sumOf { it.size.toLong() } + scopedTerminals.values.sumOf { it.size.toLong() }} " +
        "scopedAttachmentPairs=${scopedLocals.size} scopedControlPairs=${scopedPorts.size} " +
        "callMethods=${graph.methodCount} callEdges=${graph.edgeCount} " +
        "ownBridgeMemberships=${ownBridges.values.sumOf { it.size.toLong() }} ownerFamilies=${ownerVisibility.familyCount} " +
        ownerVisibility.statistics.let {
            "ownerComponents=${it.components} ownerDagEdges=${it.dagEdges} ownerIndexSeedMemberships=${it.seedMemberships} " +
                "ownerIndexWords=${it.allocatedWords} ownerIndexBytes=${it.allocatedWords * Long.SIZE_BYTES} ownerIndexBuildNanos=${it.buildNanos}"
        } + (ownerStatistics?.let {
            " ownerBitQueries=${it[0]} ownerBitHits=${it[1]} ownerOutsideQueries=${it[2]} ownerOutsideHits=${it[3]}"
        } ?: "")
    private class Owners(val familyId: Int, val graphIds: IntArray, val outsideGraph: Set<CommonMethod>)
    private class BridgeRows(val geometry: GuidanceGeometry, val labels: LongArray, val owners: List<Owners>,
                             val outputs: StaticOutputOrdinals)
    private class EntryGeometryRows(val entries: List<Pattern>, val rowIds: IntArray,
                                  val outputs: StaticOutputOrdinals)
    /** The trie owns geometries; concrete entries and exclusions remain in the original rows. */
    private class EntryDirectory(val blocks: List<EntryGeometryRows>, val spatial: PathTrie<Int>) {
        fun visit(actual: Pattern, selection: StaticLabelSelection, visit: (Pattern, Int) -> Boolean): Boolean =
            spatial.visitAroundWhile(actual.fact.base, actual.fact.path.toIntArray()) { id ->
                val block = blocks[id]
                block.outputs.visit(selection) { i -> visit(block.entries[i], block.rowIds[i]) }
            }
        companion object {
            fun build(ap: ApManager, entries: List<Pattern>): EntryDirectory {
                val grouped = LinkedHashMap<Pattern, MutableList<Int>>()
                for ((id, entry) in entries.withIndex()) {
                    ap.cancellation.checkpoint()
                    val geometry = entry.copy(fact = entry.fact.copy(mark = MarkSlot.STAR))
                    grouped.getOrPut(geometry) { ArrayList() }.add(id)
                }
                val spatial = PathTrie<Int>(ap.cancellation)
                val blocks = ArrayList<EntryGeometryRows>(grouped.size)
                for ((geometry, ids) in grouped) {
                    val outputs = StaticOutputOrdinals.Builder(ap.marks)
                    val originals = ids.map { entries[it] }
                    for (entry in originals) outputs.add(when (val mark = entry.fact.mark) {
                        is MarkSlot.Star -> GuidanceMarks.Flow
                        is MarkSlot.Concrete -> GuidanceMarks.Mapped(null,
                            if (entry.fact.base == AccessPathBase.Zero) null else mark.mark)
                    })
                    spatial.add(geometry.fact.base, geometry.fact.path.toIntArray(), blocks.size)
                    blocks += EntryGeometryRows(originals, ids.toIntArray(), outputs.build())
                }
                return EntryDirectory(blocks, spatial)
            }
        }
    }
    private class EntryRows(val entry: Pattern, val owners: Owners)
    private class BoundaryGeometryRows(val ids: IntArray, val geometry: GuidanceGeometry,
                                       val outputs: StaticOutputOrdinals)
    /** Local row IDs stay unchanged; the trie now selects their complete geometry first. */
    private class BoundaryDirectory(val blocks: List<BoundaryGeometryRows>, val spatial: PathTrie<Int>) {
        fun ids(base: AccessPathBase, path: IntArray, prefixes: Boolean = false,
                query: StaticRowQuery = StaticRowQuery.ALL): Sequence<Int> = sequence {
            val candidates = if (prefixes) spatial.lookupPrefixes(base, path) else spatial.around(base, path)
            for (id in candidates) {
                val block = blocks[id]
                val selection = if (query.mappedGeometryAllowed(block.geometry.to)) query.labels else StaticLabelSelection.FlowOnly
                val ordinals = block.outputs.ordinals(selection, query.includeFlow)
                while (ordinals.hasNext()) yield(block.ids[ordinals.nextInt()])
            }
        }
        fun around(base: AccessPathBase, path: IntArray): List<Int> = ids(base, path).toList()
        fun lookupPrefixes(base: AccessPathBase, path: IntArray): List<Int> = ids(base, path, true).toList()
        fun visitAroundWhile(base: AccessPathBase, path: IntArray, visit: (Int) -> Boolean): Boolean {
            for (id in ids(base, path)) if (!visit(id)) return false
            return true
        }
        companion object {
            fun build(ap: ApManager, rows: List<StaticGuidanceEdge>): BoundaryDirectory {
                val grouped = LinkedHashMap<GuidanceGeometry, MutableList<Int>>()
                for ((id, row) in rows.withIndex()) {
                    ap.cancellation.checkpoint()
                    grouped.getOrPut(GuidanceGeometry.of(row)) { ArrayList() }.add(id)
                }
                val spatial = PathTrie<Int>(ap.cancellation)
                val blocks = ArrayList<BoundaryGeometryRows>(grouped.size)
                for ((geometry, ids) in grouped) {
                    val outputs = StaticOutputOrdinals.Builder(ap.marks)
                    for (id in ids) { ap.cancellation.checkpoint(); outputs.add(rows[id].marks) }
                    spatial.add(geometry.to.fact.base, geometry.to.fact.path.toIntArray(), blocks.size)
                    blocks += BoundaryGeometryRows(ids.toIntArray(), geometry, outputs.build())
                }
                return BoundaryDirectory(blocks, spatial)
            }
        }
    }
    private class Attachments(
        val writerRows: List<StaticGuidanceEdge>,
        val writers: BoundaryDirectory,
        val writerSources: PathTrie<Int>,
        val readerRows: List<StaticGuidanceEdge>,
        val readers: BoundaryDirectory,
        val coloredOutputs: SelectorRows,
        val writerEntries: EntryDirectory,
        val readerEntries: EntryDirectory,
        val flowReaders: PathTrie<Int>,
        val readerSources: PathTrie<Int>,
    )
    /** Exact FULL and GROUP buckets do not need a group atom to probe an actual full mark. */
    private class SelectorRows(private val ap: ApManager) {
        private val exact = HashMap<TaintMark, LongArrayList>()
        private val groups = HashMap<GroupId, LongArrayList>()
        fun add(mark: TaintMark, row: Long) {
            ap.cancellation.checkpoint()
            if (mark == TaintMark.ZERO) return
            val map = if (ap.marks.isGroup(mark)) null else exact.getOrPut(mark) { LongArrayList() }
            if (map != null) map.add(row)
            else groups.getOrPut(ap.marks.groupOf(mark)) { LongArrayList() }.add(row)
        }
        fun candidates(mark: TaintMark): Sequence<Long> = sequence {
            if (mark == TaintMark.ZERO) return@sequence
            for (rows in listOfNotNull(exact[mark], groups[ap.marks.groupOf(mark)])) {
                val cursor = rows.iterator()
                while (cursor.hasNext()) { ap.cancellation.checkpoint(); yield(cursor.nextLong()) }
            }
        }
        fun estimate(mark: TaintMark): Long = if (mark == TaintMark.ZERO) 0 else
            (exact[mark]?.size?.toLong() ?: 0) + (groups[ap.marks.groupOf(mark)]?.size?.toLong() ?: 0)
    }


    private val scopedKeys: Map<OwnedScope, List<ScopedSummaryKey>> =
        (scopedPorts + scopedLocals.keys + scopedTerminals.keys).distinct().groupBy {
            OwnedScope(it.method, it.reversed().scope)
        }

    override fun scopedViews(): Sequence<Pair<OwnedScope, FrozenCompletion>> = scopedKeys.asSequence().map { (owner, keys) ->
        owner to ScopedView(owner, keys)
    }

    override fun local(method: MethodKey): StaticDemandView = View(method, false)
    override fun visible(method: MethodKey): StaticDemandView = View(method, true)
    override fun mayNeedInheritedPairs(method: MethodKey): Boolean =
        bridgeOwners.isNotEmpty() && !(bridgeOwners.size == 1 && method.method in bridgeOwners)

    override fun mayNeedInheritedEntries(method: MethodKey, actual: List<Pattern>): Boolean =
        mayNeedInheritedEntries(method, actual, locals[method])

    private fun mayNeedInheritedEntries(method: MethodKey, actual: List<Pattern>, local: Attachments?): Boolean {
        if (bridgeOwners.isEmpty() || bridgeOwners.size == 1 && method.method in bridgeOwners) return false
        for (leaf in actual) {
            ap.cancellation.checkpoint()
            if (leaf.fact.base == STATIC) {
                if (!bridgeEnds.visitAroundWhile(STATIC, leaf.fact.path.toIntArray()) { false }) return true
            } else if (leaf.fact.mark is MarkSlot.Concrete && leaf.fact.mark.mark != TaintMark.ZERO && local != null) {
                if (!local.readers.visitAroundWhile(leaf.fact.base, leaf.fact.path.toIntArray()) {
                        local.readerRows[it].marks != GuidanceMarks.Flow
                    }) return true
            }
        }
        return false
    }

    override fun visitPossibleTargets(method: MethodKey, actual: Pattern, visit: (Pattern, Boolean) -> Boolean): Boolean =
        visitPossibleTargets(actual, locals[method], includeBridges = true, visit)

    private fun visitPossibleTargets(actual: Pattern, local: Attachments?, includeBridges: Boolean,
                                     visit: (Pattern, Boolean) -> Boolean): Boolean {
        val localIndex = if (actual.fact.base == STATIC) local?.writerEntries else local?.readerEntries
        val selection = outputCovering(actual, ap.marks)
        if (localIndex != null && !localIndex.visit(actual, selection) { entry, _ ->
                ap.cancellation.checkpoint()
                visit(entry, entry.fact.mark is MarkSlot.Star)
            }) return false
        if (!includeBridges || actual.fact.base != STATIC) return true
        return bridgeEntries.visit(actual, selection) { entry, _ ->
            ap.cancellation.checkpoint()
            visit(entry, entry.fact.mark is MarkSlot.Star)
        }
    }

    private inner class ScopedView(private val owner: OwnedScope,
                                   private val keys: List<ScopedSummaryKey>) : FrozenCompletion {
        override fun statistics(): String = "scopedRows=${keys.size} shared=true ${this@ReferenceFrozenStaticCompletion.statistics()}"

        override fun selectExit(exit: PortId?): FrozenCompletion = if (exit == null) this
            else ScopedView(owner, keys.filter { it.scope.entry == exit })

        private fun view(method: MethodKey, inherited: Boolean): StaticDemandView {
            require(method == owner.method) { "A scoped completion retains its original method key" }
            val selected = keys.map { View(method, inherited, scopedLocals[it], scopedTerminals[it].orEmpty()) }
            return if (selected.isEmpty()) View(method, inherited, null, emptyList())
                else unionStaticDemandViews(selected)
        }

        override fun local(method: MethodKey): StaticDemandView = view(method, false)
        override fun visible(method: MethodKey): StaticDemandView = view(method, true)
        override fun mayNeedInheritedPairs(method: MethodKey): Boolean =
            this@ReferenceFrozenStaticCompletion.mayNeedInheritedPairs(method)

        override fun mayNeedInheritedEntries(method: MethodKey, actual: List<Pattern>): Boolean {
            require(method == owner.method)
            if (keys.isEmpty()) return this@ReferenceFrozenStaticCompletion.mayNeedInheritedEntries(method, actual, null)
            return keys.any { this@ReferenceFrozenStaticCompletion.mayNeedInheritedEntries(method, actual, scopedLocals[it]) }
        }

        override fun visitPossibleTargets(method: MethodKey, actual: Pattern,
                                          visit: (Pattern, Boolean) -> Boolean): Boolean {
            require(method == owner.method)
            for (key in keys) if (!this@ReferenceFrozenStaticCompletion.visitPossibleTargets(actual, scopedLocals[key],
                    includeBridges = false, visit)) return false
            return this@ReferenceFrozenStaticCompletion.visitPossibleTargets(actual, null, includeBridges = true, visit)
        }
    }

    private inner class View(private val method: MethodKey, private val inherited: Boolean,
                             private val local: Attachments? = locals[method],
                             private val terminalInputs: List<Pattern> = terminalReaders[method].orEmpty()) : C5StaticDemandView {
        override fun targetInputs(): Sequence<Pattern> = terminalInputs.asSequence()
        private val ownId = graph.id(method.method)
        private val ownRows = ownBridges[method.method] ?: LongArray(0)
        private fun eligible(owners: Owners): Boolean {
            ap.cancellation.checkpoint()
            if (!inherited) return method.method in owners.outsideGraph ||
                (ownId != null && owners.graphIds.binarySearch(ownId) >= 0)
            ownerStatistics?.incrementAndGet(2)
            if (method.method in owners.outsideGraph) {
                ownerStatistics?.incrementAndGet(3)
                return true
            }
            ap.cancellation.checkpoint()
            ownerStatistics?.incrementAndGet(0)
            val answer = ownerVisibility.contains(ownId, owners.familyId)
            if (answer) ownerStatistics?.incrementAndGet(1)
            return answer
        }

        private fun rows(id: Int, flowOnly: Boolean = false,
                         keep: StaticCandidateFilter? = null,
                         query: StaticRowQuery = StaticRowQuery.ALL): Sequence<StaticGuidanceEdge> = sequence {
            val row = bridges[id]
            val selection = if (flowOnly) StaticLabelSelection.FlowOnly else query.labels
            val allowMapped = query.mappedGeometryAllowed(row.geometry.to)
            val ordinals = row.outputs.ordinals(if (allowMapped) selection else StaticLabelSelection.FlowOnly, query.includeFlow)
            while (ordinals.hasNext()) {
                ap.cancellation.checkpoint()
                val i = ordinals.nextInt()
                val label = row.labels[i]
                val marks = if (keep == null) null else unpackBridgeMarks(label)
                if (keep != null && !keep.keep(row.geometry.from, row.geometry.to, checkNotNull(marks))) continue
                val allowed = if (inherited) eligible(row.owners[i])
                    else ownRows.binarySearch((id.toLong() shl 32) or i.toLong()) >= 0
                if (allowed) yield(if (marks == null) row.geometry.edge(label) else row.geometry.edge(marks))
            }
        }
        private fun candidates(index: PathTrie<Int>, pattern: Pattern, prefixes: Boolean): List<Int> =
            if (prefixes) index.lookupPrefixes(pattern.fact.base, pattern.fact.path.toIntArray())
            else index.around(pattern.fact.base, pattern.fact.path.toIntArray())

        private fun entries(directory: EntryDirectory, actual: Pattern, selection: StaticLabelSelection,
                            bridge: Boolean): Sequence<Pattern> = sequence {
            for (id in directory.spatial.around(actual.fact.base, actual.fact.path.toIntArray())) {
                val block = directory.blocks[id]
                val ordinals = block.outputs.ordinals(selection)
                while (ordinals.hasNext()) {
                    ap.cancellation.checkpoint()
                    val i = ordinals.nextInt()
                    val entry = block.entries[i]
                    if (!markSub(entry.fact.mark, actual.fact.mark, ap.marks)) continue
                    // Full MethodKey already scopes local W/R. Only B projections check owners.
                    if (bridge && !eligible(bridgeEntryRows[block.rowIds[i]].owners)) continue
                    yield(entry)
                }
            }
        }
        override fun entries(actual: Pattern): Sequence<Pattern> = sequence {
            val selection = outputCovering(actual, ap.marks)
            val localEntries = if (actual.fact.base == STATIC) local?.writerEntries else local?.readerEntries
            if (localEntries != null) yieldAll(entries(localEntries, actual, selection, false))
            if (actual.fact.base == STATIC) yieldAll(entries(bridgeEntries, actual, selection, true))
        }

        override fun targets(actual: Pattern, prefixesOnly: Boolean): Sequence<StaticGuidanceEdge> =
            targetsImpl(actual, prefixesOnly, null)
        override fun c5Targets(actual: Pattern, prefixesOnly: Boolean, keep: StaticCandidateFilter) =
            targetsImpl(actual, prefixesOnly, keep)
        override fun selectedTargets(actual: Pattern, prefixesOnly: Boolean, query: StaticRowQuery,
                                     keep: StaticCandidateFilter) = targetsImpl(actual, prefixesOnly, keep, query)
        private fun targetsImpl(actual: Pattern, prefixesOnly: Boolean,
                                keep: StaticCandidateFilter?, query: StaticRowQuery = StaticRowQuery.ALL): Sequence<StaticGuidanceEdge> = sequence {
            ap.cancellation.checkpoint()
            if (local != null) {
                val index = if (actual.fact.base == STATIC) local.writers else local.readers
                val rows = if (actual.fact.base == STATIC) local.writerRows else local.readerRows
                for (id in index.ids(actual.fact.base, actual.fact.path.toIntArray(), prefixesOnly, query)) {
                    ap.cancellation.checkpoint()
                    val row = rows[id]
                    if (keep == null || keep.keep(row.from, row.to, row.marks)) yield(row)
                }
            }
            if (actual.fact.base == STATIC) for (id in candidates(bridgeEnds, actual, prefixesOnly))
                yieldAll(rows(id, keep = keep, query = query))
        }

        override fun flowTargets(actual: Pattern): Sequence<StaticGuidanceEdge> = sequence {
            ap.cancellation.checkpoint()
            if (actual.fact.base == STATIC) {
                for (id in candidates(flowEnds, actual, false)) yieldAll(rows(id, true))
            } else if (local != null) for (id in candidates(local.flowReaders, actual, false)) {
                ap.cancellation.checkpoint(); yield(local.readerRows[id])
            }
        }

        override fun pairs(initial: InitialAp, outputs: List<Pattern>): Sequence<StaticGuidanceEdge> = sequence {
            val path = initial.path?.toIntArray() ?: EMPTY_PATH
            val sourceIds = HashSet<Int>()
            if (local != null) {
                // Each ID is scoped to exactly one backing row family; never intersect W and R IDs.
                val sourceIndex = if (initial.base == STATIC) local.writerSources else local.readerSources
                for (output in outputs) sourceIndex.visitAround(output.fact.base, output.fact.path.toIntArray()) {
                    sourceIds += it
                }
                val targetIndex = if (initial.base == STATIC) local.writers else local.readers
                val rows = if (initial.base == STATIC) local.writerRows else local.readerRows
                for (id in targetIndex.lookupPrefixes(initial.base, path)) {
                    ap.cancellation.checkpoint()
                    if (id in sourceIds) yield(rows[id])
                }
            }
            if (initial.base != STATIC) return@sequence
            sourceIds.clear()
            for (output in outputs) if (output.fact.base == STATIC)
                bridgeStarts.visitAround(STATIC, output.fact.path.toIntArray()) { sourceIds += it }
            for (id in bridgeEnds.lookupPrefixes(STATIC, path)) {
                ap.cancellation.checkpoint()
                if (id in sourceIds) yieldAll(rows(id))
            }
        }

        override fun incoming(input: Pattern, flowOnly: Boolean): Sequence<StaticGuidanceEdge> =
            incomingImpl(input, flowOnly, null)
        override fun c5Incoming(input: Pattern, flowOnly: Boolean, keep: StaticCandidateFilter) =
            incomingImpl(input, flowOnly, keep)
        override fun selectedIncoming(input: Pattern, query: StaticRowQuery,
                                      keep: StaticCandidateFilter) = incomingImpl(input, false, keep, query)
        private fun incomingImpl(input: Pattern, flowOnly: Boolean,
                                 keep: StaticCandidateFilter?, query: StaticRowQuery = StaticRowQuery.ALL): Sequence<StaticGuidanceEdge> = sequence {
            ap.cancellation.checkpoint()
            if (input.fact.base != STATIC) return@sequence
            val index = if (flowOnly) flowEnds else bridgeEnds
            for (id in candidates(index, input, false)) yieldAll(rows(id, flowOnly, keep, query))
            if (!flowOnly && local != null) for (id in local.writers.ids(input.fact.base, input.fact.path.toIntArray(), query = query)) {
                ap.cancellation.checkpoint()
                val row = local.writerRows[id]
                if (keep == null || keep.keep(row.from, row.to, row.marks)) yield(row)
            }
        }

        override fun outgoing(output: Pattern): Sequence<StaticGuidanceEdge> = sequence {
            ap.cancellation.checkpoint()
            for (id in candidates(flowStarts, output, false)) yieldAll(rows(id, true))
        }

        override fun markedOutputs(mark: TaintMark): Sequence<Pattern> = sequence {
            ap.cancellation.checkpoint()
            if (local != null) for (id in local.coloredOutputs.candidates(mark)) {
                val output = local.writerRows[id.toInt()].to
                if (ap.marks.coversAtom((output.fact.mark as MarkSlot.Concrete).mark, mark)) yield(output)
            }
            for (ref in coloredBridgeOutputs.candidates(mark)) {
                ap.cancellation.checkpoint()
                val rows = bridges[(ref ushr 32).toInt()]
                val i = ref.toInt()
                if (if (inherited) !eligible(rows.owners[i]) else ownRows.binarySearch(ref) < 0) continue
                val output = rows.geometry.edge(rows.labels[i]).to
                if (ap.marks.coversAtom((output.fact.mark as MarkSlot.Concrete).mark, mark)) yield(output)
            }
        }
        override fun estimatedMarkedOutputs(mark: TaintMark): Long =
            (local?.coloredOutputs?.estimate(mark) ?: 0) + coloredBridgeOutputs.estimate(mark)

        override fun hasComposedEndpoints(initial: InitialAp, outputs: List<Pattern>): Boolean =
            hasComposedEndpointsImpl(initial, outputs, null)
        override fun c5HasComposedEndpoints(initial: InitialAp, outputs: List<Pattern>,
                                            keepTarget: StaticCandidateFilter): Boolean =
            hasComposedEndpointsImpl(initial, outputs, keepTarget)
        override fun selectedHasComposedEndpoints(initial: InitialAp, outputs: List<Pattern>, query: StaticRowQuery,
                                                  keep: StaticCandidateFilter): Boolean =
            hasComposedEndpointsImpl(initial, outputs, keep, query)
        private fun hasComposedEndpointsImpl(initial: InitialAp, outputs: List<Pattern>,
                                             keepTarget: StaticCandidateFilter?, query: StaticRowQuery = StaticRowQuery.ALL): Boolean {
            ap.cancellation.checkpoint()
            val path = initial.path?.toIntArray() ?: EMPTY_PATH
            val target = if (initial.base == STATIC)
                bridgeEnds.lookupPrefixes(STATIC, path).any { rows(it, keep = keepTarget, query = query).iterator().hasNext() }
            else local?.readers?.ids(initial.base, path, true, query)?.any { id ->
                val row = local.readerRows[id]
                keepTarget == null || keepTarget.keep(row.from, row.to, row.marks)
            } == true
            if (!target) return false
            for (leaf in outputs) {
                ap.cancellation.checkpoint()
                if (leaf.fact.base == STATIC) {
                    if (bridgeStarts.around(STATIC, leaf.fact.path.toIntArray()).any { rows(it).iterator().hasNext() }) return true
                } else if (local?.writerSources?.around(leaf.fact.base, leaf.fact.path.toIntArray())?.isNotEmpty() == true)
                    return true
            }
            return false
        }

        override fun hasMarkedOutput(input: Pattern, mark: TaintMark): Boolean {
            if (mark == TaintMark.ZERO) return false
            val query = StaticRowQuery(ap.marks.staticSelector(mark)?.let(StaticLabelSelection::OutputCovers)
                ?: StaticLabelSelection.All, includeFlow = false)
            fun matches(output: Pattern): Boolean = output.fact.mark is MarkSlot.Concrete &&
                ap.marks.coversAtom(output.fact.mark.mark, mark) && joins(output, input)
            if (local != null) for (id in local.writers.ids(STATIC, input.fact.path.toIntArray(), query = query)) {
                ap.cancellation.checkpoint()
                if (matches(local.writerRows[id].to)) return true
            }
            return !bridgeEnds.visitAroundWhile(STATIC, input.fact.path.toIntArray()) { id ->
                for (edge in rows(id, query = query)) if (edge.marks != GuidanceMarks.Flow && matches(edge.to)) return@visitAroundWhile false
                true
            }
        }

    }

    internal fun joins(output: Pattern, input: Pattern): Boolean =
        staticAnchor(ap, output) == staticAnchor(ap, input) && overlap(output, input)

    class Builder(private val ap: ApManager, private val graph: DetachedStaticCallGraph) {
        private val bridges = LinkedHashMap<GuidanceGeometry, Long2ObjectLinkedOpenHashMap<MutableSet<CommonMethod>>>()
        private val localRows = LinkedHashMap<MethodKey, Pair<MutableSet<StaticGuidanceEdge>, MutableSet<StaticGuidanceEdge>>>()
        private val terminalReaders = LinkedHashMap<MethodKey, MutableSet<Pattern>>()
        private val scopedLocalRows = LinkedHashMap<ScopedSummaryKey, Pair<MutableSet<StaticGuidanceEdge>, MutableSet<StaticGuidanceEdge>>>()
        private val scopedTerminals = LinkedHashMap<ScopedSummaryKey, MutableSet<Pattern>>()
        private val scopedPorts = LinkedHashSet<ScopedSummaryKey>()

        /** An entered scope can borrow shared B/carry even without local W/R attachments. */
        fun addScopedBoundary(producer: ScopedSummaryKey) {
            ap.cancellation.checkpoint()
            scopedPorts += producer
        }

        /** Producer ports stay paired. The run-2 view reverses them without copying the graph. */
        fun addScopedSeed(producer: ScopedSummaryKey, from: Pattern, to: Pattern) {
            ap.cancellation.checkpoint()
            addScopedBoundary(producer)
            if (!RuntimeDataDomain.base(from.fact.base) || !RuntimeDataDomain.base(to.fact.base)) return
            val fromStatic = staticAnchor(ap, from) != null
            val toStatic = staticAnchor(ap, to) != null
            if (fromStatic && toStatic) addBridge(producer.method, StaticGuidanceEdge.of(from, to))
            else {
                if (fromStatic == toStatic || !fromStatic && from.fact.base == STATIC || !toStatic && to.fact.base == STATIC) return
                val rows = scopedLocalRows.getOrPut(producer) { LinkedHashSet<StaticGuidanceEdge>() to LinkedHashSet() }
                val edge = StaticGuidanceEdge.of(from, to)
                if (toStatic) rows.first += edge else rows.second += edge
            }
        }

        fun addScopedTarget(producer: ScopedSummaryKey, from: Pattern) {
            ap.cancellation.checkpoint()
            addScopedBoundary(producer)
            if (!RuntimeDataDomain.base(from.fact.base) || staticAnchor(ap, from) == null) return
            check(from.fact.mark is MarkSlot.Concrete)
            scopedTerminals.getOrPut(producer) { LinkedHashSet() }.add(guidancePattern(from))
        }

        /** Only an anonymous DEMAND terminal is an endpoint of this guidance graph. */
        fun addTarget(method: MethodKey, from: Pattern) {
            ap.cancellation.checkpoint()
            if (!RuntimeDataDomain.base(from.fact.base) || staticAnchor(ap, from) == null) return
            check(from.fact.mark is MarkSlot.Concrete) { "A terminal reader needs a concrete input mark" }
            terminalReaders.getOrPut(method) { LinkedHashSet() }.add(guidancePattern(from))
        }

        /** Phase B accepts only frozen seeds. Caller binding has finished and
         * no composition result is fed back to that earlier phase. */
        fun addSeed(method: MethodKey, from: Pattern, to: Pattern) {
            ap.cancellation.checkpoint()
            if (!RuntimeDataDomain.base(from.fact.base) || !RuntimeDataDomain.base(to.fact.base)) return
            val fromStatic = staticAnchor(ap, from) != null
            val toStatic = staticAnchor(ap, to) != null
            if (fromStatic && toStatic) addBridge(method, StaticGuidanceEdge.of(from, to))
            else addBoundary(method, from, to)
        }

        fun addSeed(method: MethodKey, edge: StaticGuidanceEdge) = addSeed(method, edge.from, edge.to)

        fun addBridge(method: MethodKey, edge: StaticGuidanceEdge) {
            ap.cancellation.checkpoint()
            check(staticAnchor(ap, edge.from) != null && staticAnchor(ap, edge.to) != null)
            val rows = bridges.getOrPut(GuidanceGeometry.of(edge)) { Long2ObjectLinkedOpenHashMap() }
            val label = packBridgeMarks(edge.marks)
            val owners = rows.get(label) ?: LinkedHashSet<CommonMethod>().also { rows.put(label, it) }
            owners += method.method
        }

        fun addBoundary(method: MethodKey, from: Pattern, to: Pattern) {
            ap.cancellation.checkpoint()
            if (!RuntimeDataDomain.base(from.fact.base) || !RuntimeDataDomain.base(to.fact.base)) return
            val fromStatic = staticAnchor(ap, from) != null
            val toStatic = staticAnchor(ap, to) != null
            if (fromStatic == toStatic) return
            // Do not reinterpret a broad static endpoint as a method-local attachment.
            if (!fromStatic && from.fact.base == STATIC || !toStatic && to.fact.base == STATIC) return
            val rows = localRows.getOrPut(method) { LinkedHashSet<StaticGuidanceEdge>() to LinkedHashSet() }
            val edge = StaticGuidanceEdge.of(from, to)
            if (toStatic) rows.first += edge else rows.second += edge
        }

        fun build(): ReferenceFrozenStaticCompletion {
            ap.cancellation.checkpoint()
            val frozenBridges = ArrayList<BridgeRows>()
            val ends = PathTrie<Int>(ap.cancellation)
            val starts = PathTrie<Int>(ap.cancellation)
            val flowStarts = PathTrie<Int>(ap.cancellation)
            val flowEnds = PathTrie<Int>(ap.cancellation)
            val coloredOutputs = SelectorRows(ap)
            val bridgeOwners = LinkedHashSet<CommonMethod>()
            val own = LinkedHashMap<CommonMethod, LongArrayList>()
            val projectedEntries = LinkedHashMap<Pattern, MutableSet<CommonMethod>>()
            var memberships = 0L
            val ownerFamilies = ArrayList<Owners>()
            fun freezeOwners(methods: Set<CommonMethod>): Owners {
                val owners = Owners(ownerFamilies.size,
                    methods.mapNotNull { ap.cancellation.checkpoint(); graph.id(it) }.toIntArray().also { it.sort() },
                    methods.filterTo(LinkedHashSet()) { ap.cancellation.checkpoint(); graph.id(it) == null })
                ownerFamilies += owners
                return owners
            }
            for ((geometry, rows) in bridges) {
                ap.cancellation.checkpoint()
                val labels = LongArray(rows.size)
                val owners = ArrayList<Owners>(rows.size)
                val ordinals = StaticOutputOrdinals.Builder(ap.marks)
                for ((index, row) in rows.long2ObjectEntrySet().withIndex()) {
                    ap.cancellation.checkpoint()
                    labels[index] = row.longKey
                    ordinals.add(unpackBridgeMarks(row.longKey))
                    val methods = row.value
                    val entry = geometry.edge(row.longKey).to
                    projectedEntries.getOrPut(entry) { LinkedHashSet() }.addAll(methods)
                    bridgeOwners += methods
                    for (method in methods) own.getOrPut(method) { LongArrayList() }
                        .add((frozenBridges.size.toLong() shl 32) or index.toLong())
                    memberships += methods.size
                    owners += freezeOwners(methods)
                    if (row.longKey == 0L) {
                        flowStarts.add(STATIC, geometry.from.fact.path.toIntArray(), frozenBridges.size)
                        flowEnds.add(STATIC, geometry.to.fact.path.toIntArray(), frozenBridges.size)
                    } else {
                        val output = (unpackBridgeMarks(row.longKey) as GuidanceMarks.Mapped).output!!
                        coloredOutputs.add(output, (frozenBridges.size.toLong() shl 32) or index.toLong())
                    }
                }
                ends.add(STATIC, geometry.to.fact.path.toIntArray(), frozenBridges.size)
                starts.add(STATIC, geometry.from.fact.path.toIntArray(), frozenBridges.size)
                frozenBridges += BridgeRows(geometry, labels, owners, ordinals.build())
            }
            fun freezeAttachments(rows: Pair<Set<StaticGuidanceEdge>, Set<StaticGuidanceEdge>>): Attachments {
                ap.cancellation.checkpoint()
                val writerSources = PathTrie<Int>(ap.cancellation)
                val colors = SelectorRows(ap)
                val flowReaders = PathTrie<Int>(ap.cancellation)
                val readerSources = PathTrie<Int>(ap.cancellation)
                val writerRows = rows.first.toList()
                val readerRows = rows.second.toList()
                for ((id, row) in writerRows.withIndex()) {
                    writerSources.add(row.from.fact.base, row.from.fact.path.toIntArray(), id)
                    (row.to.fact.mark as? MarkSlot.Concrete)?.let { colors.add(it.mark, id.toLong()) }
                }
                for ((id, row) in readerRows.withIndex()) {
                    readerSources.add(row.from.fact.base, row.from.fact.path.toIntArray(), id)
                    if (row.marks == GuidanceMarks.Flow) flowReaders.add(row.to.fact.base, row.to.fact.path.toIntArray(), id)
                }
                return Attachments(writerRows, BoundaryDirectory.build(ap, writerRows), writerSources,
                    readerRows, BoundaryDirectory.build(ap, readerRows), colors,
                    EntryDirectory.build(ap, writerRows.map { it.to }.distinct()),
                    EntryDirectory.build(ap, readerRows.map { it.to }.distinct()), flowReaders, readerSources)
            }
            val locals = localRows.mapValues { (_, rows) -> ap.cancellation.checkpoint(); freezeAttachments(rows) }
            val scoped = scopedLocalRows.mapValues { (_, rows) -> ap.cancellation.checkpoint(); freezeAttachments(rows) }
            val entryRows = ArrayList<EntryRows>()
            for ((entry, methods) in projectedEntries) {
                ap.cancellation.checkpoint()
                entryRows += EntryRows(entry, freezeOwners(methods))
            }
            // Both original B labels and their projected entry families now have stable IDs.
            val visibilityBuilder = FrozenOwnerVisibility.Builder(graph, ownerFamilies.size, ap.cancellation)
            for (family in ownerFamilies) {
                ap.cancellation.checkpoint()
                for (owner in family.graphIds) visibilityBuilder.seed(family.familyId, owner)
            }
            val visibility = visibilityBuilder.finish()
            return ReferenceFrozenStaticCompletion(ap, graph, frozenBridges, ends, starts, flowStarts, flowEnds, coloredOutputs,
                Collections.unmodifiableSet(bridgeOwners), own.mapValues { it.value.toLongArray() },
                entryRows, EntryDirectory.build(ap, entryRows.map { it.entry }),
                Collections.unmodifiableMap(locals),
                Collections.unmodifiableMap(terminalReaders.mapValues { Collections.unmodifiableList(it.value.toList()) }),
                Collections.unmodifiableMap(scoped),
                Collections.unmodifiableMap(scopedTerminals.mapValues { Collections.unmodifiableList(it.value.toList()) }),
                Collections.unmodifiableSet(LinkedHashSet(scopedPorts)), visibility,
                memberships, localRows.values.sumOf { it.first.size.toLong() } + scopedLocalRows.values.sumOf { it.first.size.toLong() },
                localRows.values.sumOf { it.second.size.toLong() } + scopedLocalRows.values.sumOf { it.second.size.toLong() })
        }
    }
}
