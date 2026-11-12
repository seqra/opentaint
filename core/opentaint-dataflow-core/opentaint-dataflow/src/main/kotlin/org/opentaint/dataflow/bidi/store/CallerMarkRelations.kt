package org.opentaint.dataflow.bidi.store

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import org.opentaint.dataflow.bidi.ap.*

/** Literal source/target pairs at one field position and exact/any slot. */
internal class CallerMarkRelation {
    private var diagonal = MarkSet.EMPTY
    private val changingByTarget = Int2ObjectOpenHashMap<MarkSet>()

    fun add(source: TaintMark, targets: MarkSet) {
        if (source in targets) diagonal += source
        for (target in targets.ids) if (target != source.id) {
            changingByTarget.put(target, (changingByTarget.get(target) ?: MarkSet.EMPTY) + source)
        }
    }

    fun targets(source: TaintMark): MarkSet {
        val ids = ArrayList<Int>()
        if (source in diagonal) ids += source.id
        val it = changingByTarget.int2ObjectEntrySet().fastIterator()
        while (it.hasNext()) {
            val entry = it.next()
            if (source in entry.value) ids += entry.intKey
        }
        return if (ids.isEmpty()) MarkSet.EMPTY else MarkSet(ids.toIntArray())
    }

    fun remove(source: TaintMark) {
        val one = MarkSet.of(source)
        diagonal -= one
        val it = changingByTarget.int2ObjectEntrySet().fastIterator()
        while (it.hasNext()) {
            val entry = it.next()
            val rest = entry.value - one
            if (rest.isEmpty) it.remove() else entry.setValue(rest)
        }
    }

    val isEmpty: Boolean get() = diagonal.isEmpty && changingByTarget.isEmpty()
    val diagonalCount: Int get() = diagonal.size
    val changingPairCount: Long get() = changingByTarget.values.sumOf { it.size.toLong() }
    val changingTargetCount: Int get() = changingByTarget.size
}

/** One header/owner family shares geometry. Source postings select complete packets. */
internal class CallerMarkRelations(private val m: ApManager) {
    /** Output coordinates belong to this family, not the manager's strong premise-path interner. */
    private class Coordinate(path: IntArray) {
        val path = path.copyOf()
        private val hash = this.path.contentHashCode()
        override fun hashCode(): Int = hash
        override fun equals(other: Any?): Boolean = this === other ||
            other is Coordinate && hash == other.hash && path.contentEquals(other.path)
    }
    private class Cell(val coordinate: Coordinate) {
        val exact = CallerMarkRelation()
        val any = CallerMarkRelation()
        val isEmpty: Boolean get() = exact.isEmpty && any.isEmpty
    }

    private val cells = HashMap<Coordinate, Cell>()
    private val cellsBySource = Int2ObjectOpenHashMap<LinkedHashSet<Cell>>()
    val sourceCount: Int get() = cellsBySource.size
    val cellCount: Int get() = cells.size
    val diagonalCount: Long get() = cells.values.sumOf { it.exact.diagonalCount.toLong() + it.any.diagonalCount }
    val changingPairCount: Long get() = cells.values.sumOf { it.exact.changingPairCount + it.any.changingPairCount }
    val changingTargetCount: Long get() = cells.values.sumOf { it.exact.changingTargetCount.toLong() + it.any.changingTargetCount }

    fun add(source: TaintMark, root: TaintNode) {
        val sourceCells = cellsBySource.getOrPut(source.id) { LinkedHashSet() }
        m.taintAlg.forEachLeaf(root, EMPTY_PATH, m.cancellation) { path, leaf ->
            val coordinate = Coordinate(path)
            val cell = cells.getOrPut(coordinate) { Cell(coordinate) }
            cell.exact.add(source, leaf.exact)
            cell.any.add(source, leaf.any)
            sourceCells += cell
        }
    }

    fun remove(source: TaintMark) {
        for (cell in cellsBySource.remove(source.id) ?: return) {
            m.cancellation.checkpoint()
            cell.exact.remove(source)
            cell.any.remove(source)
            if (cell.isEmpty) cells.remove(cell.coordinate)
        }
    }

    private class BuildNode {
        var exact = MarkSet.EMPTY
        var any = MarkSet.EMPTY
        val children = Int2ObjectOpenHashMap<BuildNode>()
        var built: TaintNode? = null
    }
    private class BuildFrame(val node: BuildNode, var expanded: Boolean = false)

    /** Reconstruct only the selected source's cells. The walk is stack safe. */
    fun root(source: TaintMark): TaintNode {
        val selected = checkNotNull(cellsBySource.get(source.id))
        val root = BuildNode()
        for (cell in selected) {
            m.cancellation.checkpoint()
            var at = root
            for (accessor in cell.coordinate.path) {
                m.cancellation.checkpoint()
                at = at.children.getOrPut(accessor) { BuildNode() }
            }
            at.exact = cell.exact.targets(source)
            at.any = cell.any.targets(source)
        }
        val pending = ArrayDeque<BuildFrame>()
        pending.addLast(BuildFrame(root))
        while (pending.isNotEmpty()) {
            m.cancellation.checkpoint()
            val frame = pending.last()
            if (!frame.expanded) {
                frame.expanded = true
                for (child in frame.node.children.values) pending.addLast(BuildFrame(child))
                continue
            }
            val node = frame.node
            val keys = node.children.keys.toIntArray().sortedArray()
            node.built = m.taintAlg.node(m.taintLeaves(node.exact, node.any), keys,
                Array(keys.size) { checkNotNull(node.children.get(keys[it]).built) })
            pending.removeLast()
        }
        return checkNotNull(root.built)
    }
}
