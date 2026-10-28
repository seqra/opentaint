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
import java.util.concurrent.atomic.AtomicLong

/** Virtual demand only. A lookup neither starts a query nor changes publication permission. */
interface FrozenCompletion {
    fun statistics(): String = "unavailable"
    fun near(method: MethodKey, actual: Pattern): Sequence<DemandPattern>
    fun covering(method: MethodKey, initial: InitialAp): Sequence<DemandPattern>
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
    fun edge(label: Long): StaticGuidanceEdge {
        val marks = unpackBridgeMarks(label)
        return when (marks) {
            GuidanceMarks.Flow -> StaticGuidanceEdge(from, to, marks)
            is GuidanceMarks.Mapped -> StaticGuidanceEdge(
                from.copy(fact = from.fact.copy(mark = MarkSlot.Concrete(checkNotNull(marks.input)))),
                to.copy(fact = to.fact.copy(mark = MarkSlot.Concrete(checkNotNull(marks.output)))), marks)
        }
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

private data class StaticAnchor(val owner: Int, val field: Int?)

/** Exact class markers do not denote the fields of the class. Root/class FLOW is not a graph vertex. */
private fun staticAnchor(ap: ApManager, pattern: Pattern): StaticAnchor? {
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

    internal fun scratch(method: CommonMethod, cancellation: Cancellation): Reachability =
        Reachability(ids[method], adjacency, cancellation)

    internal fun id(method: CommonMethod): Int? = ids[method]

    /** Incremental query scratch: a graph vertex is expanded at most once per lookup. */
    internal class Reachability(root: Int?, private val graph: Array<IntArray>, private val cancellation: Cancellation) {
        private val seen = HashSet<Int>()
        private val pending = ArrayDeque<Int>()
        init { if (root != null) { seen += root; pending += root } }
        fun reachesAny(owners: IntArray): Boolean {
            if (owners.any { it in seen }) return true
            while (pending.isNotEmpty()) {
                cancellation.checkpoint()
                val next = pending.removeLast()
                var hit = false
                for (child in graph[next]) {
                    cancellation.checkpoint()
                    if (seen.add(child)) pending += child
                    if (owners.binarySearch(child) >= 0) hit = true
                }
                if (hit) return true
            }
            return false
        }
    }

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
    private val locals: Map<MethodKey, Attachments>,
    val seedMemberships: Long,
    val writerAttachments: Long,
    val readerAttachments: Long,
) : FrozenCompletion {
    private val counters = if (java.lang.Boolean.getBoolean("org.opentaint.bidi.optimizationStatistics"))
        Array(3) { AtomicLong() } else null
    val seedKeys: Int get() = bridges.sumOf { it.labels.size }
    val seedGeometries: Int get() = bridges.size
    override fun statistics(): String = "seedKeys=$seedKeys seedGeometries=$seedGeometries ownerMemberships=$seedMemberships " +
        "writerAttachments=$writerAttachments readerAttachments=$readerAttachments " +
        "callMethods=${graph.methodCount} callEdges=${graph.edgeCount}" +
        (counters?.let { " lookups=${it[0].get()} states=${it[1].get()} emitted=${it[2].get()}" } ?: "")
    private class Owners(val graphIds: IntArray, val outsideGraph: Set<CommonMethod>)
    private class BridgeRows(val geometry: GuidanceGeometry, val labels: LongArray, val owners: List<Owners>)
    private class Attachments(val writers: PathTrie<StaticGuidanceEdge>, val readers: PathTrie<StaticGuidanceEdge>)
    private data class Walk(val current: Pattern, val target: Pattern, val marks: GuidanceMarks)

    override fun near(method: MethodKey, actual: Pattern): Sequence<DemandPattern> = lookup(method, actual, false)
    override fun covering(method: MethodKey, initial: InitialAp): Sequence<DemandPattern> = lookup(method, initial.toPattern(), true)

    /** Reverse search starts at a forward result. Its finite state retains colored round trips beside FLOW. */
    private fun lookup(method: MethodKey, actual: Pattern, prefixesOnly: Boolean): Sequence<DemandPattern> = sequence {
        ap.cancellation.checkpoint()
        counters?.get(0)?.incrementAndGet()
        val reach = graph.scratch(method.method, ap.cancellation)
        val local = locals[method]
        val pending = ArrayDeque<Walk>()
        val visited = HashSet<Walk>()
        val emitted = HashSet<DemandPattern>()
        fun candidates(index: PathTrie<StaticGuidanceEdge>, pattern: Pattern): List<StaticGuidanceEdge> =
            if (prefixesOnly) index.lookupPrefixes(pattern.fact.base, pattern.fact.path.toIntArray())
            else index.around(pattern.fact.base, pattern.fact.path.toIntArray())
        fun offer(edge: StaticGuidanceEdge) {
            val state = Walk(edge.from, edge.to, edge.marks)
            if (visited.add(state)) { pending += state; counters?.get(1)?.incrementAndGet() }
        }
        if (local != null) for (reader in candidates(local.readers, actual)) {
            ap.cancellation.checkpoint()
            offer(reader)
        }
        fun bridgeRows(id: Int): Sequence<StaticGuidanceEdge> = sequence {
            val rows = bridges[id]
            for (index in rows.labels.indices) {
                ap.cancellation.checkpoint()
                val owned = rows.owners[index]
                if (method.method in owned.outsideGraph || reach.reachesAny(owned.graphIds))
                    yield(rows.geometry.edge(rows.labels[index]))
            }
        }
        if (actual.fact.base == STATIC) {
            val ids = if (prefixesOnly) bridgeEnds.lookupPrefixes(STATIC, actual.fact.path.toIntArray())
                else bridgeEnds.around(STATIC, actual.fact.path.toIntArray())
            for (id in ids) {
                ap.cancellation.checkpoint()
                for (edge in bridgeRows(id)) offer(edge)
            }
            if (local != null) for (writer in candidates(local.writers, actual)) {
                ap.cancellation.checkpoint()
                offer(writer)
            }
        }
        while (pending.isNotEmpty()) {
            ap.cancellation.checkpoint()
            val state = pending.removeFirst()
            val guide = DemandPattern(state.target, state.current)
            if (emitted.add(guide)) { counters?.get(2)?.incrementAndGet(); yield(guide) }
            if (state.current.fact.base != STATIC) continue
            for (id in bridgeEnds.around(STATIC, state.current.fact.path.toIntArray())) {
                ap.cancellation.checkpoint()
                for (edge in bridgeRows(id)) compose(edge, state)?.let(::offer)
            }
            if (local != null) for (writer in local.writers.around(STATIC, state.current.fact.path.toIntArray())) {
                ap.cancellation.checkpoint()
                compose(writer, state)?.let(::offer)
            }
        }
    }

    private fun compose(left: StaticGuidanceEdge, right: Walk): StaticGuidanceEdge? {
        if (staticAnchor(ap, left.to) != staticAnchor(ap, right.current) || !overlap(left.to, right.current)) return null
        val label = composeMarks(left.marks, right.marks) ?: return null
        val fromMark = when (label) {
            GuidanceMarks.Flow -> MarkSlot.STAR
            is GuidanceMarks.Mapped -> if (left.from.fact.base == AccessPathBase.Zero) left.from.fact.mark
                else MarkSlot.Concrete(checkNotNull(label.input))
        }
        val toMark = when (label) {
            GuidanceMarks.Flow -> MarkSlot.STAR
            is GuidanceMarks.Mapped -> if (right.target.fact.base == AccessPathBase.Zero) right.target.fact.mark
                else MarkSlot.Concrete(checkNotNull(label.output))
        }
        return StaticGuidanceEdge(left.from.copy(fact = left.from.fact.copy(mark = fromMark)),
            right.target.copy(fact = right.target.fact.copy(mark = toMark)), label)
    }

    private fun composeMarks(left: GuidanceMarks, right: GuidanceMarks): GuidanceMarks? = when (left) {
        GuidanceMarks.Flow -> right
        is GuidanceMarks.Mapped -> when (right) {
            GuidanceMarks.Flow -> left
            is GuidanceMarks.Mapped -> if (left.output != null && right.input != null &&
                (ap.marks.coversAtom(left.output, right.input) || ap.marks.coversAtom(right.input, left.output)))
                GuidanceMarks.Mapped(left.input, right.output) else null
        }
    }

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
            var memberships = 0L
            for ((geometry, rows) in bridges) {
                ap.cancellation.checkpoint()
                val labels = LongArray(rows.size)
                val owners = ArrayList<Owners>(rows.size)
                for ((index, row) in rows.long2ObjectEntrySet().withIndex()) {
                    ap.cancellation.checkpoint()
                    labels[index] = row.longKey
                    val methods = row.value
                    memberships += methods.size
                    owners += Owners(methods.mapNotNull { graph.id(it) }.toIntArray().also { it.sort() },
                        methods.filterTo(LinkedHashSet()) { graph.id(it) == null })
                }
                ends.add(STATIC, geometry.to.fact.path.toIntArray(), frozenBridges.size)
                frozenBridges += BridgeRows(geometry, labels, owners)
            }
            val locals = LinkedHashMap<MethodKey, Attachments>()
            for ((method, rows) in localRows) {
                ap.cancellation.checkpoint()
                val writers = PathTrie<StaticGuidanceEdge>(ap.cancellation)
                val readers = PathTrie<StaticGuidanceEdge>(ap.cancellation)
                for (row in rows.first) writers.add(STATIC, row.to.fact.path.toIntArray(), row)
                for (row in rows.second) readers.add(row.to.fact.base, row.to.fact.path.toIntArray(), row)
                locals[method] = Attachments(writers, readers)
            }
            return FrozenStaticCompletion(ap, graph, frozenBridges, ends, Collections.unmodifiableMap(locals),
                memberships, localRows.values.sumOf { it.first.size.toLong() },
                localRows.values.sumOf { it.second.size.toLong() })
        }
    }
}
