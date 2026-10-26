package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import java.util.ArrayDeque
import java.util.IdentityHashMap

/** Exact diagonal relations for the current runtime atoms.
 * A row has one immutable typed output geometry and two exact mark masks.
 * No original scalar tree or historical row is retained behind the masks. */
class DiagonalRelations(private val m: ApManager, private val interners: StoreInterners = m.newInterners()) {
    private data class Header(val initial: InitialAp, val base: AccessPathBase, val layer: Layer,
                              val tail: Tail, val exclusion: ExclusionSet)
    private class Masks(var marks: MarkSet, var protected: MarkSet)
    private val headers = LinkedHashMap<Header, LinkedHashMap<FlowNode, Masks>>()

    val isEmpty: Boolean get() = headers.isEmpty()
    val rowCount: Int get() = headers.values.sumOf { it.size }
    val markMembershipCount: Int get() = headers.values.sumOf { rows -> rows.values.sumOf { it.marks.size } }

    /** Scan exact masks without constructing their scalar decoded trees. */
    fun census(): RelationCensus = census(RelationCensusCounter(m.cancellation))

    internal fun census(counter: RelationCensusCounter): RelationCensus {
        m.cancellation.checkpoint()
        var result = RelationCensus.ZERO
        for (rows in headers.values) for ((shape, masks) in rows) {
            m.cancellation.checkpoint()
            val outputs = counter.flowAnnotations(shape)
            result += RelationCensus(
                concreteOutputMemberships = Math.multiplyExact(outputs, masks.marks.size.toLong()),
                protectedOutputMemberships = Math.multiplyExact(outputs, masks.protected.size.toLong()),
                diagonalGeometryRows = 1,
                diagonalMarkRows = masks.marks.size.toLong(),
            )
        }
        return result
    }

    /** Same-geometry mask admission. Null selects the scalar fallback before
     * mutation; an empty list means the whole offered mask was already stored.
     * Different geometry for an overlapping mark needs the existing spatial
     * subtraction/protection adapter and is deliberately not guessed here. */
    fun addDiagonal(delta: DiagonalDelta): List<DiagonalDelta>? {
        m.cancellation.checkpoint()
        require(delta.initialShape.manager === m) { "A diagonal packet must use this AP manager" }
        val header = Header(delta.initialShape, delta.base, delta.layer, delta.tail, delta.exclusion)
        val previous = headers[header]
        if (previous != null) for ((shape, masks) in previous) {
            m.cancellation.checkpoint()
            if (!(masks.marks intersect delta.marks).isEmpty && shape != delta.geometry) return null
        }
        val old = previous?.get(delta.geometry)
        val fresh = m.intern(delta.marks - (old?.marks ?: MarkSet.EMPTY))
        val flagged = if (delta.protected)
            m.intern(delta.marks - (old?.protected ?: MarkSet.EMPTY)) else MarkSet.EMPTY
        if (fresh.isEmpty && flagged.isEmpty) return emptyList()
        val rows = previous ?: LinkedHashMap<FlowNode, Masks>().also { headers[header] = it }
        admit(rows, delta.geometry, delta.marks, if (delta.protected) delta.marks else MarkSet.EMPTY)
        val output = ArrayList<DiagonalDelta>(2)
        if (!delta.protected && !fresh.isEmpty) output += delta.copy(marks = fresh, protected = false)
        if (!flagged.isEmpty) output += delta.copy(marks = flagged, protected = true)
        return output
    }

    fun supports(premise: PremiseKey, facts: Facts): Boolean {
        m.cancellation.checkpoint()
        val f = facts as? TaintTree ?: return false
        if ((f.anyTail != Tail.STAR && f.anyTail != Tail.ANY) ||
            flowInitialForCoverage(m, premise) == null) return false
        val mark = ((premise as InitialAp).mark as MarkSlot.Concrete).mark
        val all = m.taintAlg.foldAll(f.root, m.cancellation)
        if (!all.exact.isEmpty || all.any != m.markSetOf(mark)) return false
        val flags = f.nonSubsumable?.let { m.taintAlg.foldAll(it, m.cancellation) }
        return flags == null || (flags.exact.isEmpty && flags.any.isSubsetOf(all.any))
    }

    /** Admit geometry/mask memberships before constructing the one scalar
     * delta needed by the current interpreter interface. */
    fun add(premise: PremiseKey, facts: Facts): Facts? {
        require(supports(premise, facts)) { "Only admitted diagonal STAR or ANY relations use this store" }
        val f = facts as TaintTree
        val initial = premise as InitialAp
        val mark = (initial.mark as MarkSlot.Concrete).mark
        val one = m.markSetOf(mark)
        val header = Header(checkNotNull(flowInitialForCoverage(m, premise)), f.base, f.layer, f.anyTail, f.exclusion)
        val rows = headers.getOrPut(header) { LinkedHashMap() }
        val offered = geometry(f.root)
        val offeredFlags = f.nonSubsumable?.let(::geometry)
        var fresh: FlowNode? = offered
        var freshFlags: FlowNode? = null
        var upgrades: FlowNode? = null

        // Capture only current rows for this operation. Mutations below replace
        // their mask membership; this list is not retained by the owner.
        for ((shape, masks) in rows.entries.toList()) {
            m.cancellation.checkpoint()
            if (mark !in masks.marks) continue
            fresh = fresh?.let { subtract(it, shape, header.tail) }
            if (mark in masks.protected) {
                freshFlags = union(freshFlags, overlap(offered, shape, header.tail))
                continue
            }
            val upgrade = offeredFlags?.let { overlap(shape, it, header.tail) } ?: continue
            upgrades = union(upgrades, upgrade)
            removeMark(rows, shape, masks, one)
            subtractExact(shape, upgrade)?.let { admit(rows, it, one, MarkSet.EMPTY) }
            admit(rows, upgrade, one, one)
        }
        if (fresh != null) {
            if (offeredFlags != null) freshFlags = union(freshFlags, overlap(fresh, offeredFlags, header.tail))
            freshFlags = freshFlags?.let { overlap(fresh, it, header.tail) }
            val plain = freshFlags?.let { subtractExact(fresh, it) } ?: if (freshFlags == null) fresh else null
            if (plain != null) admit(rows, plain, one, MarkSet.EMPTY)
            if (freshFlags != null) admit(rows, freshFlags, one, one)
        }
        val delta = union(fresh, upgrades) ?: return null
        val protectedDelta = union(freshFlags, upgrades)
        return decode(header, delta, mark, protectedDelta)
    }

    fun all(): Sequence<Pair<PremiseKey, Facts>> = sequence {
        m.cancellation.checkpoint()
        for ((header, rows) in headers) for ((shape, masks) in rows) for (id in masks.marks.ids) {
            m.cancellation.checkpoint()
            val mark = TaintMark(id)
            yield(markedInitial(header.initial, mark) to decode(header, shape, mark,
                if (mark in masks.protected) shape else null))
        }
    }

    fun borrow(premise: PremiseKey): Sequence<Facts> = sequence {
        m.cancellation.checkpoint()
        val initial = premise as? InitialAp ?: return@sequence
        val mark = (initial.mark as? MarkSlot.Concrete)?.mark ?: return@sequence
        val flow = flowInitialForCoverage(m, initial) ?: return@sequence
        for ((header, rows) in headers) {
            if (header.initial !== flow) continue
            for ((shape, masks) in rows) {
                m.cancellation.checkpoint()
                if (mark in masks.marks) yield(decode(header, shape, mark,
                    if (mark in masks.protected) shape else null))
            }
        }
    }

    /** Remove plain diagonal outputs covered by one complete typed FLOW row. */
    fun compact(flowInitial: InitialAp, flowFacts: FlowTree) {
        m.cancellation.checkpoint()
        if (!flowInitial.isFlow || (flowInitial.tail != Tail.STAR && flowInitial.tail != Tail.ANY) ||
            (flowFacts.tail != Tail.STAR && flowFacts.tail != Tail.ANY)) return
        for ((header, rows) in headers.entries.toList()) {
            if (header.initial !== flowInitial || header.base != flowFacts.base || header.tail != flowFacts.tail ||
                (flowFacts.layer == Layer.DEMAND && header.layer == Layer.NORMAL) ||
                (header.tail == Tail.STAR && !flowFacts.exclusion.isSubsetOf(header.exclusion))) continue
            for ((shape, masks) in rows.entries.toList()) {
                m.cancellation.checkpoint()
                val selected = m.intern((masks.marks - masks.protected) - flowFacts.markExclusion)
                if (selected.isEmpty) continue
                val rest = subtract(shape, flowFacts.root, header.tail)
                if (rest === shape || rest == shape) continue
                removeMark(rows, shape, masks, selected)
                if (rest != null) admit(rows, rest, selected, MarkSet.EMPTY)
            }
            if (rows.isEmpty()) headers.remove(header)
        }
    }

    private fun markedInitial(flow: InitialAp, mark: TaintMark): InitialAp =
        m.initial(flow.base, flow.path, flow.tail, flow.exclusion, MarkSlot.Concrete(mark))

    private fun removeMark(rows: MutableMap<FlowNode, Masks>, shape: FlowNode, masks: Masks, marks: MarkSet) {
        masks.marks = m.intern(masks.marks - marks)
        masks.protected = m.intern(masks.protected - marks)
        if (masks.marks.isEmpty) rows.remove(shape)
    }

    private fun admit(rows: MutableMap<FlowNode, Masks>, geometry: FlowNode, marks: MarkSet, protected: MarkSet) {
        val shape = interners.flow.internIfRequired(geometry)
        val masks = rows[shape]
        if (masks == null) rows[shape] = Masks(m.intern(marks), m.intern(protected))
        else {
            masks.marks = m.intern(masks.marks + marks)
            masks.protected = m.intern(masks.protected + protected)
        }
    }

    private fun union(a: FlowNode?, b: FlowNode?): FlowNode? = when {
        a == null -> b
        b == null -> a
        else -> FlowAlgebra.mergeAdd(a, b, m.cancellation)
    }

    private fun subtract(a: FlowNode, b: FlowNode, tail: Tail): FlowNode? =
        if (tail == Tail.STAR) subtractExact(a, b) else subtractCovered(a, b)

    private fun overlap(a: FlowNode, b: FlowNode, tail: Tail): FlowNode? {
        if (tail != Tail.STAR) return overlap(a, b)
        val outside = subtractExact(a, b) ?: return a
        return subtractExact(a, outside)
    }

    private fun subtractCovered(a: FlowNode, b: FlowNode): FlowNode? = FlowAlgebra.subtract(a, b, FlowLeaf.NONE,
        at = { it }, below = { it }, cancellation = m.cancellation)

    private fun subtractExact(a: FlowNode, b: FlowNode): FlowNode? = FlowAlgebra.subtract(a, b, FlowLeaf.NONE,
        at = { it }, below = { FlowLeaf.NONE }, cancellation = m.cancellation)

    private class Frame<N>(val node: N, var next: Int = 0)

    /** Convert shape once; marks do not enter the geometry key. */
    private fun geometry(root: TaintNode): FlowNode {
        val memo = IdentityHashMap<TaintNode, FlowNode>()
        val stack = ArrayDeque<Frame<TaintNode>>()
        stack.addLast(Frame(root))
        while (stack.isNotEmpty()) {
            m.cancellation.checkpoint()
            val frame = stack.peekLast()
            val kids = frame.node.childData
            if (kids != null && frame.next < kids.size) {
                val child = kids[frame.next++]
                if (!memo.containsKey(child)) stack.addLast(Frame(child))
                continue
            }
            memo[frame.node] = FlowAlgebra.node(if (frame.node.leaf.any.isEmpty) FlowLeaf.NONE else FlowLeaf.LEAF,
                frame.node.accessorData, kids?.map { memo.getValue(it) }?.toTypedArray())
            stack.removeLast()
        }
        return memo.getValue(root)
    }

    private fun scalar(root: FlowNode, mark: TaintMark): TaintNode {
        val memo = IdentityHashMap<FlowNode, TaintNode>()
        val stack = ArrayDeque<Frame<FlowNode>>()
        val leaf = m.taintLeaves(MarkSet.EMPTY, m.markSetOf(mark))
        stack.addLast(Frame(root))
        while (stack.isNotEmpty()) {
            m.cancellation.checkpoint()
            val frame = stack.peekLast()
            val kids = frame.node.childData
            if (kids != null && frame.next < kids.size) {
                val child = kids[frame.next++]
                if (!memo.containsKey(child)) stack.addLast(Frame(child))
                continue
            }
            memo[frame.node] = m.taintAlg.node(if (frame.node.leaf.isEmpty) TaintLeaves.EMPTY else leaf,
                frame.node.accessorData, kids?.map { memo.getValue(it) }?.toTypedArray())
            stack.removeLast()
        }
        return memo.getValue(root)
    }

    private fun decode(header: Header, shape: FlowNode, mark: TaintMark, protected: FlowNode?): TaintTree =
        m.taintTree(header.base, header.layer, scalar(shape, mark), header.exclusion, anyTail = header.tail,
            nonSubsumable = protected?.let { scalar(it, mark) })

    private class OverlapKey(val shape: FlowNode, val protected: FlowNode?, val above: Boolean) {
        override fun hashCode(): Int = (System.identityHashCode(shape) * 31 + System.identityHashCode(protected)) * 31 + above.hashCode()
        override fun equals(other: Any?): Boolean = other is OverlapKey && shape === other.shape &&
            protected === other.protected && above == other.above
    }
    private class OverlapFrame(val key: OverlapKey, var expanded: Boolean = false)

    /** Keep original output leaves which intersect protected ANY regions.
     * A protected descendant upgrades the containing original leaf. */
    private fun overlap(shape: FlowNode, protected: FlowNode): FlowNode? {
        val memo = HashMap<OverlapKey, FlowNode?>()
        val stack = ArrayDeque<OverlapFrame>()
        val initial = OverlapKey(shape, protected, false)
        stack.addLast(OverlapFrame(initial))
        while (stack.isNotEmpty()) {
            m.cancellation.checkpoint()
            val frame = stack.peekLast()
            val key = frame.key
            if (memo.containsKey(key)) { stack.removeLast(); continue }
            if (key.above) { memo[key] = key.shape; stack.removeLast(); continue }
            if (key.protected == null) { memo[key] = null; stack.removeLast(); continue }
            val next = !key.protected.leaf.isEmpty
            fun childKey(accessor: Int, child: FlowNode) = OverlapKey(child, key.protected.child(accessor), next)
            if (!frame.expanded) {
                frame.expanded = true
                key.shape.accessorData?.forEachIndexed { i, accessor ->
                    val child = childKey(accessor, key.shape.childData!![i])
                    if (!memo.containsKey(child)) stack.addLast(OverlapFrame(child))
                }
            } else {
                memo[key] = FlowAlgebra.mapChildren(key.shape, key.shape.leaf, m.cancellation) { accessor, child ->
                    memo.getValue(childKey(accessor, child))
                }
                stack.removeLast()
            }
        }
        return memo.getValue(initial)
    }
}
