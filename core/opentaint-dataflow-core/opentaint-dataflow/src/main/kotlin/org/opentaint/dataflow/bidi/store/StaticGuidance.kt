package org.opentaint.dataflow.bidi.store

import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.ints.IntLinkedOpenHashSet
import it.unimi.dsi.fastutil.longs.Long2IntOpenHashMap
import it.unimi.dsi.fastutil.longs.Long2ObjectLinkedOpenHashMap
import it.unimi.dsi.fastutil.longs.LongArrayList
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.CommonMethod
import java.util.Collections
import java.util.concurrent.atomic.AtomicLongArray

/** Virtual demand only. A lookup neither starts a query nor changes publication permission. */
interface FrozenCompletion {
    fun statistics(): String = "unavailable"

    /** Immutable primitive seed indexes. LOCAL has own common-method B plus exact-context W/R. */
    fun local(method: MethodKey): StaticDemandView
    fun visible(method: MethodKey): StaticDemandView

    /** Conservative target envelope: visibility can be ignored, emission cannot. */
    fun visitPossibleTargets(method: MethodKey, actual: Pattern, visit: (Pattern, Boolean) -> Boolean): Boolean
    fun mayNeedInheritedEntries(method: MethodKey, actual: List<Pattern>): Boolean
    fun mayNeedInheritedPairs(method: MethodKey): Boolean
}

interface StaticDemandView {
    fun entries(actual: Pattern): Sequence<Pattern>
    fun targets(actual: Pattern, prefixesOnly: Boolean = false): Sequence<StaticGuidanceEdge>
    fun flowTargets(actual: Pattern): Sequence<StaticGuidanceEdge>
    fun pairs(initial: InitialAp, outputs: List<Pattern>): Sequence<StaticGuidanceEdge>
    fun incoming(input: Pattern, flowOnly: Boolean = false): Sequence<StaticGuidanceEdge>
    fun outgoing(output: Pattern): Sequence<StaticGuidanceEdge>
    fun markedOutputs(mark: TaintMark): Sequence<Pattern>
    fun estimatedMarkedOutputs(mark: TaintMark): Long
    fun hasMarkedOutput(input: Pattern, mark: TaintMark): Boolean
    fun hasComposedEndpoints(initial: InitialAp, outputs: List<Pattern>): Boolean
}

/** Handoff keeps STAR correlation. Only abstract demand drops its field exclusion. */
fun guidancePattern(pattern: Pattern): Pattern {
    val located = if (pattern.fact.tail == Tail.ANY_TAINT)
        pattern.copy(fact = pattern.fact.copy(tail = Tail.ANY), exclusion = ExclusionSet.Empty)
    else pattern
    val mark = if (located.fact.mark is MarkSlot.Star) MarkSlot.STAR else located.fact.mark
    return normalizeDemandFieldExclusion(located.copy(fact = located.fact.copy(
        path = Collections.unmodifiableList(ArrayList(located.fact.path)), mark = mark)))
}

/** Endpoints retain geometry; only the mark relation composes. Null is a private ZERO selector. */
sealed interface GuidanceMarks {
    data object Flow : GuidanceMarks
    data class Mapped(val input: TaintMark?, val output: TaintMark?) : GuidanceMarks
}

data class StaticGuidanceEdge(val from: Pattern, val to: Pattern, val marks: GuidanceMarks) {
    companion object {
        fun of(from: Pattern, to: Pattern): StaticGuidanceEdge {
            val a = guidancePattern(from)
            val b = guidancePattern(to)
            val marks = if (a.fact.mark is MarkSlot.Star && b.fact.mark is MarkSlot.Star) GuidanceMarks.Flow
            else {
                // K6/S7: a FLOW original has only FLOW conclusions. Concrete guarded
                // GEN uses a concrete origin (or the real ZERO), never a mixed row.
                check(a.fact.mark is MarkSlot.Concrete && b.fact.mark is MarkSlot.Concrete) {
                    "A colored guidance row needs concrete endpoints; FLOW is diagonal"
                }
                GuidanceMarks.Mapped(
                    if (a.fact.base == AccessPathBase.Zero) null else a.fact.mark.mark,
                    if (b.fact.base == AccessPathBase.Zero) null else b.fact.mark.mark,
                )
            }
            return StaticGuidanceEdge(a, b, marks)
        }
    }
}

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

/** Run-1 actors share B geometry once and pack its exact mark pairs in primitive words. */
class StaticGuidanceInterner(private val ap: ApManager) {
    private val geometryIds = HashMap<GuidanceGeometry, Int>()
    private val geometries = ArrayList<GuidanceGeometry>()
    private val ids = ArrayList<Long2IntOpenHashMap>()
    private val rowGeometry = IntArrayList()
    private val rowLabels = LongArrayList()
    @Synchronized fun intern(edge: StaticGuidanceEdge): Int {
        ap.cancellation.checkpoint()
        val geometry = GuidanceGeometry.of(edge)
        val geometryId = geometryIds.getOrPut(geometry) {
            geometries.size.also { geometries += geometry; ids += Long2IntOpenHashMap().apply { defaultReturnValue(-1) } }
        }
        val label = packBridgeMarks(edge.marks)
        val old = ids[geometryId].get(label)
        if (old >= 0) return old
        val id = rowGeometry.size
        rowGeometry.add(geometryId)
        rowLabels.add(label)
        ids[geometryId].put(label, id)
        return id
    }
    @Synchronized fun row(id: Int): StaticGuidanceEdge = geometries[rowGeometry.getInt(id)].edge(rowLabels.getLong(id))
    @Synchronized fun clear() { geometryIds.clear(); geometries.clear(); ids.clear(); rowGeometry.clear(); rowLabels.clear() }
}

class StaticGuidanceSeedStore(
    private val ap: ApManager,
    private val ops: ApOps,
    private val interner: StaticGuidanceInterner,
) {
    private val memberships = IntLinkedOpenHashSet()

    /** Called after exit rules, before live static/static suppression. No Facts are retained. */
    fun add(original: PremiseKey, result: Facts) {
        ap.cancellation.checkpoint()
        check(original is InitialAp) { "Run-1 cannot contain an ND original" }
        if (original.base != STATIC || result.base != STATIC) return
        val from = original.toPattern()
        if (staticAnchor(ap, from) == null) return // broad carry is a separate symbolic family
        for (leaf in ops.leaves(result)) {
            ap.cancellation.checkpoint()
            if (staticAnchor(ap, leaf) != null) memberships.add(interner.intern(StaticGuidanceEdge.of(from, leaf)))
        }
    }

    fun frozenRows(): Sequence<StaticGuidanceEdge> = sequence {
        val iterator = memberships.iterator()
        while (iterator.hasNext()) { ap.cancellation.checkpoint(); yield(interner.row(iterator.nextInt())) }
    }
}

internal data class StaticAnchor(val owner: Int, val field: Int?)

/** Exact class markers do not denote the fields of the class. Root/class FLOW is not a graph vertex. */
internal fun staticAnchor(ap: ApManager, pattern: Pattern): StaticAnchor? {
    if (pattern.fact.base != STATIC) return null
    val path = pattern.fact.path
    if (path.isEmpty() || !path[0].isClass()) return null
    if (path.size >= 2 && ap.accessors.accessor(path[1]) is FieldAccessor) return StaticAnchor(path[0], path[1])
    return if (path.size == 1 && pattern.fact.tail == Tail.EXACT) StaticAnchor(path[0], null) else null
}

/** Only IDs and immutable adjacency survive prescan. No statement, runner or subscription is retained. */
class DetachedStaticCallGraph private constructor(
    private val ids: Map<CommonMethod, Int>,
    private val adjacency: Array<IntArray>,
) {
    val methodCount: Int get() = adjacency.size
    val edgeCount: Long get() = adjacency.sumOf { it.size.toLong() }

    internal fun id(method: CommonMethod): Int? = ids[method]
    internal fun outDegree(methodId: Int): Int = adjacency[methodId].size
    internal fun calleeAt(methodId: Int, position: Int): Int = adjacency[methodId][position]

    companion object {
        val EMPTY = DetachedStaticCallGraph(emptyMap(), emptyArray())
        fun copyOf(source: Map<CommonMethod, Set<CommonMethod>>, cancellation: Cancellation): DetachedStaticCallGraph {
            val ids = LinkedHashMap<CommonMethod, Int>()
            for ((caller, callees) in source) {
                cancellation.checkpoint()
                ids.getOrPut(caller) { ids.size }
                for (callee in callees) { cancellation.checkpoint(); ids.getOrPut(callee) { ids.size } }
            }
            val adjacency = Array(ids.size) { IntArray(0) }
            for ((caller, callees) in source) {
                cancellation.checkpoint()
                adjacency[ids.getValue(caller)] = callees.map { cancellation.checkpoint(); ids.getValue(it) }.toIntArray()
            }
            return DetachedStaticCallGraph(Collections.unmodifiableMap(ids), adjacency)
        }
    }
}

/** Incoming run-2 graph. B keys are shared; W/R remain attached to their complete MethodKey. */
class FrozenStaticCompletion private constructor(
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


    override fun local(method: MethodKey): StaticDemandView = View(method, false)
    override fun visible(method: MethodKey): StaticDemandView = View(method, true)
    override fun mayNeedInheritedPairs(method: MethodKey): Boolean =
        bridgeOwners.isNotEmpty() && !(bridgeOwners.size == 1 && method.method in bridgeOwners)

    override fun mayNeedInheritedEntries(method: MethodKey, actual: List<Pattern>): Boolean {
        if (bridgeOwners.isEmpty() || bridgeOwners.size == 1 && method.method in bridgeOwners) return false
        val local = locals[method]
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

    override fun visitPossibleTargets(method: MethodKey, actual: Pattern, visit: (Pattern, Boolean) -> Boolean): Boolean {
        val local = locals[method]
        val localIndex = if (actual.fact.base == STATIC) local?.writerEntries else local?.readerEntries
        val selection = outputCovering(actual, ap.marks)
        if (localIndex != null && !localIndex.visit(actual, selection) { entry, _ ->
                ap.cancellation.checkpoint()
                visit(entry, entry.fact.mark is MarkSlot.Star)
            }) return false
        if (actual.fact.base != STATIC) return true
        return bridgeEntries.visit(actual, selection) { entry, _ ->
            ap.cancellation.checkpoint()
            visit(entry, entry.fact.mark is MarkSlot.Star)
        }
    }

    private inner class View(private val method: MethodKey, private val inherited: Boolean) : C5StaticDemandView {
        private val ownId = graph.id(method.method)
        private val local = locals[method]
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

        /** Phase B accepts only frozen seeds. Caller binding has finished and
         * no composition result is fed back to that earlier phase. */
        fun addSeed(method: MethodKey, from: Pattern, to: Pattern) {
            ap.cancellation.checkpoint()
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
            val fromStatic = staticAnchor(ap, from) != null
            val toStatic = staticAnchor(ap, to) != null
            if (fromStatic == toStatic) return
            // Do not reinterpret a broad static endpoint as a method-local attachment.
            if (!fromStatic && from.fact.base == STATIC || !toStatic && to.fact.base == STATIC) return
            val rows = localRows.getOrPut(method) { LinkedHashSet<StaticGuidanceEdge>() to LinkedHashSet() }
            val edge = StaticGuidanceEdge.of(from, to)
            if (toStatic) rows.first += edge else rows.second += edge
        }

        fun build(): FrozenStaticCompletion {
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
            val locals = LinkedHashMap<MethodKey, Attachments>()
            for ((method, rows) in localRows) {
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
                locals[method] = Attachments(writerRows, BoundaryDirectory.build(ap, writerRows), writerSources,
                    readerRows, BoundaryDirectory.build(ap, readerRows), colors,
                    EntryDirectory.build(ap, writerRows.map { it.to }.distinct()),
                    EntryDirectory.build(ap, readerRows.map { it.to }.distinct()), flowReaders, readerSources)
            }
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
            return FrozenStaticCompletion(ap, graph, frozenBridges, ends, starts, flowStarts, flowEnds, coloredOutputs,
                Collections.unmodifiableSet(bridgeOwners), own.mapValues { it.value.toLongArray() },
                entryRows, EntryDirectory.build(ap, entryRows.map { it.entry }),
                Collections.unmodifiableMap(locals), visibility,
                memberships, localRows.values.sumOf { it.first.size.toLong() },
                localRows.values.sumOf { it.second.size.toLong() })
        }
    }
}
