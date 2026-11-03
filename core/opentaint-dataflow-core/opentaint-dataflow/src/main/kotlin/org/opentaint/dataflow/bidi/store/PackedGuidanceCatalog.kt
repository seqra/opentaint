package org.opentaint.dataflow.bidi.store

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import it.unimi.dsi.fastutil.longs.LongArrayList
import it.unimi.dsi.fastutil.longs.LongOpenHashSet
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*

/** Slots, including the real control ZERO mark, are distinct from nullable data endpoints. */
internal object BoundaryMarkCodec {
    fun pack(from: MarkSlot, to: MarkSlot): Long {
        if (from is MarkSlot.Star && to is MarkSlot.Star) return 0L
        check(from is MarkSlot.Concrete && to is MarkSlot.Concrete) {
            "A colored guidance row needs concrete endpoints; FLOW is diagonal"
        }
        val input = from.mark.id.toLong() + 1L
        val output = to.mark.id.toLong() + 1L
        return (input shl 32) or (output and 0xffffffffL)
    }
    fun input(label: Long): MarkSlot = if (label == 0L) MarkSlot.STAR
        else MarkSlot.Concrete(TaintMark((label ushr 32).toInt() - 1))
    fun output(label: Long): MarkSlot = if (label == 0L) MarkSlot.STAR
        else MarkSlot.Concrete(TaintMark(label.toInt() - 1))
    fun relation(geometry: GuidanceGeometry, label: Long): GuidanceMarks = if (label == 0L) GuidanceMarks.Flow else
        GuidanceMarks.Mapped(
            if (geometry.from.fact.base == AccessPathBase.Zero) null else (input(label) as MarkSlot.Concrete).mark,
            if (geometry.to.fact.base == AccessPathBase.Zero) null else (output(label) as MarkSlot.Concrete).mark)
}

/** Detached immutable metadata. A mark hole is installed after guidance normalization only. */
internal class PackedGuidanceCatalog private constructor(
    private val endpoints: Array<Pattern>,
    private val geometries: Array<GuidanceGeometry>,
) {
    val endpointCount: Int get() = endpoints.size
    val geometryCount: Int get() = geometries.size
    fun endpoint(id: Int): Pattern = endpoints[id]
    fun geometry(id: Int): GuidanceGeometry = geometries[id]

    class Builder {
        private var endpointIds = HashMap<Pattern, Int>()
        private val endpoints = ArrayList<Pattern>()
        private var geometryIds = HashMap<GuidanceGeometry, Int>()
        private val geometries = ArrayList<GuidanceGeometry>()
        private var indexed = true
        private fun ensureIndexes() {
            if (indexed) return
            for ((id, endpoint) in endpoints.withIndex()) endpointIds[endpoint] = id
            for ((id, geometry) in geometries.withIndex()) geometryIds[geometry] = id
            indexed = true
        }
        fun endpoint(normalized: Pattern): Int {
            ensureIndexes()
            val geometry = normalized.copy(fact = normalized.fact.copy(mark = MarkSlot.STAR))
            return endpointIds.getOrPut(geometry) { endpoints.size.also { endpoints += geometry } }
        }
        fun geometry(from: Pattern, to: Pattern): Int {
            val key = GuidanceGeometry(endpoints[endpoint(from)], endpoints[endpoint(to)])
            return geometryIds.getOrPut(key) { geometries.size.also { geometries += key } }
        }
        fun freeze(): PackedGuidanceCatalog = PackedGuidanceCatalog(endpoints.toTypedArray(), geometries.toTypedArray()).also {
            // The frozen catalog never points back to a builder or a live store.
            endpointIds = HashMap()
            geometryIds = HashMap()
            indexed = false
        }
    }
}

/** One exact owner/family's old local row ordinals, with primitive paired labels. */
internal class PackedGuidanceRows private constructor(
    private val catalog: PackedGuidanceCatalog,
    private val geometryIds: IntArray,
    private val labels: LongArray,
) {
    val size: Int get() = geometryIds.size
    fun geometry(id: Int): GuidanceGeometry = catalog.geometry(geometryIds[id])
    fun marks(id: Int): GuidanceMarks = BoundaryMarkCodec.relation(geometry(id), labels[id])
    fun isFlow(id: Int): Boolean = labels[id] == 0L
    fun from(id: Int): Pattern = geometry(id).from.withSlot(BoundaryMarkCodec.input(labels[id]))
    fun to(id: Int): Pattern = geometry(id).to.withSlot(BoundaryMarkCodec.output(labels[id]))
    fun outputMark(id: Int): TaintMark? = (BoundaryMarkCodec.output(labels[id]) as? MarkSlot.Concrete)?.mark
    fun edge(id: Int): StaticGuidanceEdge = StaticGuidanceEdge(from(id), to(id), marks(id))
    fun keptEdge(id: Int, keep: StaticCandidateFilter?): StaticGuidanceEdge? {
        val from = from(id)
        val to = to(id)
        val marks = marks(id)
        return if (keep == null || keep.keep(from, to, marks)) StaticGuidanceEdge(from, to, marks) else null
    }

    class Builder(private val catalog: PackedGuidanceCatalog.Builder) {
        private val geometries = IntArrayList()
        private val labels = LongArrayList()
        private var seen = Int2ObjectOpenHashMap<LongOpenHashSet>()
        private val projected = PackedEndpointRows.Builder(catalog)
        private var indexed = true
        private fun seenLabels(geometry: Int): LongOpenHashSet =
            seen.get(geometry) ?: LongOpenHashSet().also { seen.put(geometry, it) }
        val size: Int get() = geometries.size
        fun add(from: Pattern, to: Pattern) {
            if (!indexed) {
                for (id in 0 until geometries.size) seenLabels(geometries.getInt(id)).add(labels.getLong(id))
                indexed = true
            }
            val a = guidancePattern(from)
            val b = guidancePattern(to)
            val label = BoundaryMarkCodec.pack(a.fact.mark, b.fact.mark)
            val geometry = catalog.geometry(a, b)
            if (!seenLabels(geometry).add(label)) return
            geometries.add(geometry)
            labels.add(label)
            projected.add(b)
        }
        fun freezeEntries(catalog: PackedGuidanceCatalog): PackedEndpointRows = projected.freeze(catalog)
        fun freeze(catalog: PackedGuidanceCatalog): PackedGuidanceRows =
            PackedGuidanceRows(catalog, geometries.toIntArray(), labels.toLongArray()).also {
                seen = Int2ObjectOpenHashMap(); indexed = false
            }
    }
}

/** Entry directories read fields, so building an index does not decode every row. */
internal interface StaticEndpointRows {
    val size: Int
    fun geometry(id: Int): Pattern
    fun pattern(id: Int): Pattern
    fun marks(id: Int): GuidanceMarks
}

/** Primitive terminal memberships and primitive projected W/R entry memberships. */
internal class PackedEndpointRows private constructor(
    private val catalog: PackedGuidanceCatalog,
    private val geometryIds: IntArray,
    private val markIds: IntArray,
) : StaticEndpointRows {
    override val size: Int get() = geometryIds.size
    override fun geometry(id: Int): Pattern = catalog.endpoint(geometryIds[id])
    override fun pattern(id: Int): Pattern = geometry(id).withSlot(
        if (markIds[id] == FLOW_MARK) MarkSlot.STAR else MarkSlot.Concrete(TaintMark(markIds[id])))
    override fun marks(id: Int): GuidanceMarks = if (markIds[id] == FLOW_MARK) GuidanceMarks.Flow else
        GuidanceMarks.Mapped(null, if (geometry(id).fact.base == AccessPathBase.Zero) null else TaintMark(markIds[id]))
    fun patterns(): Sequence<Pattern> = sequence { for (id in geometryIds.indices) yield(pattern(id)) }

    class Builder(private val catalog: PackedGuidanceCatalog.Builder) {
        private val geometries = IntArrayList()
        private val marks = IntArrayList()
        private var seen = Int2ObjectOpenHashMap<IntOpenHashSet>()
        private var indexed = true
        private fun seenMarks(geometry: Int): IntOpenHashSet =
            seen.get(geometry) ?: IntOpenHashSet().also { seen.put(geometry, it) }
        val size: Int get() = geometries.size
        fun add(normalized: Pattern) {
            if (!indexed) {
                for (id in 0 until geometries.size) seenMarks(geometries.getInt(id)).add(marks.getInt(id))
                indexed = true
            }
            val id = catalog.endpoint(normalized)
            val mark = when (val slot = normalized.fact.mark) {
                is MarkSlot.Star -> FLOW_MARK
                is MarkSlot.Concrete -> slot.mark.id
            }
            if (!seenMarks(id).add(mark)) return
            geometries.add(id)
            marks.add(mark)
        }
        fun freeze(catalog: PackedGuidanceCatalog): PackedEndpointRows =
            PackedEndpointRows(catalog,geometries.toIntArray(),marks.toIntArray()).also {
                seen = Int2ObjectOpenHashMap(); indexed = false
            }
    }
    companion object { private const val FLOW_MARK = -1 }
}

private fun Pattern.withSlot(mark: MarkSlot): Pattern =
    if (fact.mark == mark) this else copy(fact = fact.copy(mark = mark))
