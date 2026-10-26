package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.interp.StatementSummary
import java.util.ArrayDeque
import org.opentaint.dataflow.util.Cancellation

/** One diagonal geometry and an exact mask. No scalar per-mark input archive is kept. */
class NeutralRelationBatch private constructor(
    private val m: ApManager,
    val initialShape: InitialAp,
    val template: TaintTree,
    marks: MarkSet,
    sharedGeometryKey: Any? = null,
) {
    var marks: MarkSet = marks; private set
    val size: Int get() = marks.size
    val markCount: Int get() = size
    val geometryKey: Any = sharedGeometryKey ?: GeometryKey(initialShape, template.groupKey,
        ShapeKey(template.root, geometryHash(m, template.root), m.cancellation),
        template.nonSubsumable?.let { ShapeKey(it, geometryHash(m, it), m.cancellation) })
    val isEmpty: Boolean get() = marks.isEmpty

    fun mergeIfSameGeometry(other: NeutralRelationBatch): Boolean {
        m.cancellation.checkpoint()
        if (m !== other.m || geometryKey != other.geometryKey) return false
        marks = m.intern(marks + other.marks)
        return true
    }

    private fun initial(mark: TaintMark): InitialAp = m.initial(initialShape.base, initialShape.path,
        initialShape.tail, initialShape.exclusion, MarkSlot.Concrete(mark))

    /** Decode only at an existing scalar boundary. Marks stay correlated with their own initials. */
    private fun decode(mark: TaintMark): TaintTree {
        val one = m.markSetOf(mark)
        fun root(n: TaintNode): TaintNode = checkNotNull(m.taintAlg.mapLeaves(n, m.cancellation) {
            m.taintLeaves(if (it.exact.isEmpty) MarkSet.EMPTY else one, if (it.any.isEmpty) MarkSet.EMPTY else one)
        })
        return m.taintTree(template.base, template.layer, root(template.root), template.exclusion, template.anyTail,
            template.nonSubsumable?.let(::root))
    }

    fun decode(): Sequence<Pair<InitialAp, TaintTree>> = sequence {
        for (id in marks.ids) {
            m.cancellation.checkpoint()
            val mark = TaintMark(id)
            yield(initial(mark) to decode(mark))
        }
    }

    /** A queue can retain the remaining exact mask when it takes the scalar fallback. */
    fun removeFirst(): Pair<InitialAp, TaintTree> {
        check(!marks.isEmpty) { "An empty batch has no scalar member" }
        val mark = TaintMark(marks.ids[0])
        marks = m.intern(marks - m.markSetOf(mark))
        return initial(mark) to decode(mark)
    }

    /** Limit one actor turn without expanding its pending mark memberships. */
    fun take(max: Int): NeutralRelationBatch {
        require(max > 0) { "A batch slice needs a positive budget" }
        check(!isEmpty) { "An empty batch has no prefix" }
        val selected = m.intern(MarkSet(marks.ids.take(max).toIntArray()))
        marks = m.intern(marks - selected)
        return NeutralRelationBatch(m, initialShape, template, selected, geometryKey)
    }

    private fun packed(): TaintTree {
        val mask = marks
        fun root(n: TaintNode): TaintNode = checkNotNull(m.taintAlg.mapLeaves(n, m.cancellation) {
            m.taintLeaves(if (it.exact.isEmpty) MarkSet.EMPTY else mask, if (it.any.isEmpty) MarkSet.EMPTY else mask)
        })
        return m.taintTree(template.base, template.layer, root(template.root), template.exclusion, template.anyTail,
            template.nonSubsumable?.let(::root))
    }

    /** Calls, endpoints, observers and rule stages are certified by the caller before this boundary.
     * A false result makes no callback and leaves the batch available for the scalar path. */
    fun applyPacked(ops: ApOps, summary: StatementSummary, mode: ApMode,
                    emit: (InitialAp, TaintTree, MarkSet) -> Unit,
                    untouched: (InitialAp, TaintTree, MarkSet) -> Unit = emit): Boolean {
        if (ops.manager !== m || !mode.run1 || mode.markMode != MarkMode.FULL ||
            isEmpty || !certifies(summary)) return false
        if (template.base !in summary.touched) {
            untouched(initialShape, packed(), marks)
            return true
        }
        val input = summary.typeFilters[template.base]?.let { ops.filter(packed(), it) } ?: if (
            summary.typeFilters.containsKey(template.base)) null else packed()
        if (input == null) return true
        // No mark-dependent primitive is admitted. The representative initial is
        // used only for the unchanged nonstatic spatial AP contract.
        val representative = initial(TaintMark(marks.ids[0]))
        val output = object : ApOut {
            override fun markRequest(mark: TaintMark): Unit = error("A certified neutral form cannot request a mark")
            override fun result(f: Facts) {
                val filtered = summary.resultFilters[f.base]?.let { ops.filter(f, it) } ?: if (
                    summary.resultFilters.containsKey(f.base)) null else f
                if (filtered == null) return
                ops.limit(filtered, mode.fieldLimit, object : ApOut {
                    override fun markRequest(mark: TaintMark): Unit = error("Field limits cannot request a mark")
                    override fun result(bounded: Facts) {
                        check(bounded is TaintTree) { "Neutral transport preserves TAINT" }
                        emit(initialShape, bounded, marks)
                    }
                })
            }
        }
        for (edge in summary.edgesOf(input.base)) {
            m.cancellation.checkpoint()
            ops.applyEdge(input, representative, edge.edge, statementEdge = true, mode = mode, out = output, may = edge.may)
        }
        return true
    }

    /** Existing scalar boundaries decode only after the form has been classified. */
    fun apply(ops: ApOps, summary: StatementSummary, mode: ApMode,
              emit: (PremiseKey, Facts) -> Unit,
              untouched: (PremiseKey, Facts) -> Unit = emit): Boolean =
        applyPacked(ops, summary, mode,
            { _, facts, mask -> emitDecoded(facts, emit, mask) },
            { _, facts, mask -> emitDecoded(facts, untouched, mask) })

    private fun emitDecoded(packed: Facts, emit: (PremiseKey, Facts) -> Unit, selected: MarkSet = marks) {
        check(packed is TaintTree) { "A nonstatic STAR-to-STAR transfer preserves TAINT" }
        decodePacked(m, initialShape, packed, selected, emit)
    }

    private data class GeometryKey(val initial: InitialAp, val header: GroupKey,
                                   val ordinary: ShapeKey, val protection: ShapeKey?)
    private class ShapeKey(val root: TaintNode, val hash: Long, val cancellation: Cancellation) {
        override fun hashCode(): Int = (hash xor (hash ushr 32)).toInt()
        override fun equals(other: Any?): Boolean = this === other || other is ShapeKey &&
            hash == other.hash && sameGeometry(root, other.root, cancellation)
    }

    companion object {
        private class HashFrame(val node: TaintNode, var next: Int = 0)
        private fun geometryHash(m: ApManager, root: TaintNode): Long {
            val memo = java.util.IdentityHashMap<TaintNode, Long>()
            val stack = ArrayDeque<HashFrame>()
            stack.addLast(HashFrame(root))
            while (stack.isNotEmpty()) {
                m.cancellation.checkpoint()
                val frame = stack.peekLast()
                val kids = frame.node.childData
                if (kids != null && frame.next < kids.size) {
                    val child = kids[frame.next++]
                    if (!memo.containsKey(child)) stack.addLast(HashFrame(child))
                    continue
                }
                var hash = (if (frame.node.leaf.exact.isEmpty) 0L else 1L) +
                    (if (frame.node.leaf.any.isEmpty) 0L else 2L)
                frame.node.accessorData?.forEachIndexed { i, accessor ->
                    hash += (memo.getValue(kids!![i]) * 31 + accessor) shl 5
                }
                memo[frame.node] = hash
                stack.removeLast()
            }
            return memo.getValue(root)
        }

        /** Scalar fallback, invoked only after packet/form admission has been classified. */
        fun decodePacked(m: ApManager, initialShape: InitialAp, packed: TaintTree, marks: MarkSet,
                         emit: (PremiseKey, Facts) -> Unit) {
            check(initialShape.manager === m && initialShape.isFlow)
            for (id in marks.ids) {
                m.cancellation.checkpoint()
                val mark = TaintMark(id)
                val one = m.markSetOf(mark)
                val root = m.taintAlg.mapLeaves(packed.root, m.cancellation) {
                    m.taintLeaves(it.exact intersect one, it.any intersect one)
                } ?: continue
                val protected = packed.nonSubsumable?.let { n -> m.taintAlg.mapLeaves(n, m.cancellation) {
                    m.taintLeaves(it.exact intersect one, it.any intersect one)
                } }
                val initial = m.initial(initialShape.base, initialShape.path, initialShape.tail,
                    initialShape.exclusion, MarkSlot.Concrete(mark))
                emit(initial, m.taintTree(packed.base, packed.layer, root, packed.exclusion, packed.anyTail, protected))
            }
        }

        /** A stored mask becomes one packed work value; no per-mark scalar input is built. */
        fun fromDiagonal(m: ApManager, delta: DiagonalDelta): NeutralRelationBatch? {
            if (delta.initialShape.manager !== m || delta.base == STATIC ||
                delta.base is AccessPathBase.CleanerTemporary || delta.marks.isEmpty ||
                delta.marks.ids.any { m.marks.isGroup(TaintMark(it)) || it == TaintMark.ZERO.id }) return null
            val leaf = m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY, delta.marks))
            val root = m.taintAlg.graft(delta.geometry, { !it.isEmpty }, leaf, m.cancellation) ?: return null
            val packed = m.taintTree(delta.base, delta.layer, root, delta.exclusion, anyTail = delta.tail,
                nonSubsumable = if (delta.protected) root else null)
            return NeutralRelationBatch(m, delta.initialShape, packed, delta.marks)
        }

        /** Certify the packet cell before any scalar result decoder is called. */
        fun toDiagonal(m: ApManager, initialShape: InitialAp, packed: TaintTree, marks: MarkSet): DiagonalDelta? {
            if (initialShape.manager !== m || initialShape.mark != MarkSlot.STAR || (initialShape.tail != Tail.STAR && initialShape.tail != Tail.ANY) || packed.base == STATIC ||
                packed.base is AccessPathBase.CleanerTemporary || (packed.anyTail != Tail.STAR && packed.anyTail != Tail.ANY) || marks.isEmpty ||
                marks.ids.any { m.marks.isGroup(TaintMark(it)) || it == TaintMark.ZERO.id }) return null
            var uniform = true
            m.taintAlg.forEachLeaf(packed.root, EMPTY_PATH, m.cancellation) { _, leaf ->
                if (!leaf.exact.isEmpty || leaf.any != marks) uniform = false
            }
            if (!uniform) return null
            val protected = packed.nonSubsumable
            if (protected != null && protected !== packed.root &&
                m.taintAlg.minusNode(packed.root, protected, m.cancellation) != null) return null
            val geometry = FlowAlgebra.graft(packed.root, { !it.any.isEmpty }, FlowAlgebra.LEAF_NODE, m.cancellation)
                ?: return null
            return DiagonalDelta(initialShape, packed.base, packed.layer, geometry, m.intern(marks), protected != null,
                packed.anyTail, packed.exclusion)
        }

        fun from(m: ApManager, premise: PremiseKey, facts: Facts): NeutralRelationBatch? {
            val initial = premise as? InitialAp ?: return null
            val mark = (initial.mark as? MarkSlot.Concrete)?.mark ?: return null
            val f = facts as? TaintTree ?: return null
            if (initial.manager !== m || mark == TaintMark.ZERO || m.marks.isGroup(mark) || initial.tail != Tail.STAR ||
                initial.exclusion != ExclusionSet.Empty || f.exclusion != ExclusionSet.Empty || f.base == STATIC ||
                f.base is AccessPathBase.CleanerTemporary) return null
            val all = m.taintAlg.foldAll(f.root, m.cancellation)
            val one = m.markSetOf(mark)
            if (!all.exact.isSubsetOf(one) || !all.any.isSubsetOf(one)) return null
            val shape = m.initial(initial.base, initial.path, initial.tail, initial.exclusion, MarkSlot.STAR)
            return NeutralRelationBatch(m, shape, f, one)
        }

        /** Only transport geometry is shared. Mark filters and every source/static hook stay scalar. */
        fun certifies(summary: StatementSummary): Boolean = summary.sources.isEmpty() &&
            summary.conjunctions.isEmpty() && summary.staticOperations.isEmpty() &&
            summary.typeFilters.values.all { it.markPolicy == null } &&
            summary.resultFilters.values.all { it.markPolicy == null } && summary.edges.all { me ->
                val e = me.edge
                !me.isSource && !me.conjunctive && me.actionId == null &&
                    e.from.base != STATIC && e.to.base != STATIC &&
                    e.from.base != AccessPathBase.Zero && e.to.base != AccessPathBase.Zero &&
                    (e.from.mark as? MarkSlot.Star)?.excluded?.isEmpty == true &&
                    (e.to.mark as? MarkSlot.Star)?.excluded?.isEmpty == true
            }

        /** Marks do not enter this comparison. The caller has already checked diagonality. */
        private fun sameGeometry(a: TaintNode?, b: TaintNode?, cancellation: Cancellation): Boolean {
            if (a === b) return true
            if (a == null || b == null) return false
            val pending = ArrayDeque<Pair<TaintNode, TaintNode>>()
            val seen = HashSet<NodePair<TaintLeaves>>()
            pending.addLast(a to b)
            while (pending.isNotEmpty()) {
                cancellation.checkpoint()
                val (x, y) = pending.removeLast()
                if (x === y) continue
                if (x.leaf.exact.isEmpty != y.leaf.exact.isEmpty || x.leaf.any.isEmpty != y.leaf.any.isEmpty ||
                    !x.accessorData.contentEquals(y.accessorData)) return false
                if (!seen.add(NodePair(x, y))) continue
                x.childData?.indices?.forEach { pending.addLast(x.childData[it] to y.childData!![it]) }
            }
            return true
        }
    }
}
