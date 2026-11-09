package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import java.util.ArrayDeque
import java.util.IdentityHashMap

/** Exact diagonal relations for the current runtime atoms.
 * A row has one immutable typed output geometry and two exact mark masks.
 * No original scalar tree or historical row is retained behind the masks. */
class DiagonalRelations(private val m: ApManager, private val interners: StoreInterners = m.newInterners()) {
    private data class Scope(val initial: InitialAp, val base: AccessPathBase, val layer: Layer)
    private data class Header(val scope: Scope, val tail: Tail, val exclusion: ExclusionSet) {
        constructor(initial: InitialAp, base: AccessPathBase, layer: Layer, tail: Tail, exclusion: ExclusionSet) :
            this(Scope(initial, base, layer), tail, exclusion)
        val initial get() = scope.initial
        val base get() = scope.base
        val layer get() = scope.layer
    }
    private class Masks(var plain: MarkSet, var protected: MarkSet) {
        val marks: MarkSet get() = plain + protected
    }
    /** The common case reuses the geometry map object. Siblings allocate no
     * second index, per-scope map or per-header entry; they stay in this scope. */
    private class Rows(val tail: Tail, val exclusion: ExclusionSet) : LinkedHashMap<FlowNode, Masks>() {
        var next: Rows? = null
    }
    private val headers = LinkedHashMap<Scope, Rows>()

    private fun findRows(header: Header): Rows? {
        var current = headers[header.scope]
        while (current != null) {
            m.cancellation.checkpoint()
            if (current.tail == header.tail && current.exclusion == header.exclusion) return current
            current = current.next
        }
        return null
    }

    private fun rowsFor(header: Header): Rows {
        var current = headers[header.scope]
            ?: return Rows(header.tail, header.exclusion).also { headers[header.scope] = it }
        while (true) {
            m.cancellation.checkpoint()
            val rows = current
            if (rows.tail == header.tail && rows.exclusion == header.exclusion) return rows
            val next = rows.next
            if (next == null) return Rows(header.tail, header.exclusion).also { rows.next = it }
            current = next
        }
    }

    private fun removeHeader(header: Header) {
        var previous: Rows? = null
        var current = headers[header.scope]
        while (current != null) {
            if (current.tail == header.tail && current.exclusion == header.exclusion) {
                if (previous == null) {
                    val next = current.next
                    if (next == null) headers.remove(header.scope) else headers[header.scope] = next
                } else previous.next = current.next
                current.next = null
                return
            }
            previous = current
            current = current.next
        }
    }

    private fun scopedRows(scope: Scope): Sequence<Pair<Header, Rows>> = sequence {
        var current = headers[scope]
        while (current != null) {
            m.cancellation.checkpoint()
            val rows = current
            yield(Header(scope, rows.tail, rows.exclusion) to rows)
            current = rows.next
        }
    }

    private fun allRows(): Sequence<Pair<Header, Rows>> = sequence {
        for (scope in headers.keys) yieldAll(scopedRows(scope))
    }

    val isEmpty: Boolean get() = headers.isEmpty()
    val rowCount: Int get() = allRows().sumOf { it.second.size }
    val markMembershipCount: Int get() = allRows().sumOf { (_, rows) -> rows.values.sumOf { it.plain.size + it.protected.size } }

    /** Scan exact masks without constructing their scalar decoded trees. */
    fun census(): RelationCensus = census(RelationCensusCounter(m.cancellation))

    internal fun census(counter: RelationCensusCounter,
                        include: (PremiseKey, Layer) -> Boolean = { _, _ -> true }): RelationCensus {
        m.cancellation.checkpoint()
        var result = RelationCensus.ZERO
        for ((header, rows) in allRows()) {
            // Diagonal scopes are nonzero singleton premises. Selection does not decode a mark.
            if (!include(header.initial, header.layer)) continue
            for ((shape, masks) in rows) {
                m.cancellation.checkpoint()
                val outputs = counter.flowAnnotations(shape)
                result += RelationCensus(
                    concreteOutputMemberships = Math.multiplyExact(outputs, (masks.plain.size + masks.protected.size).toLong()),
                    protectedOutputMemberships = Math.multiplyExact(outputs, masks.protected.size.toLong()),
                    diagonalGeometryRows = 1,
                    diagonalMarkRows = (masks.plain.size + masks.protected.size).toLong(),
                )
            }
        }
        return result
    }

    /** Same-geometry mask admission. Null selects the scalar fallback before
     * mutation; an empty list means the whole offered mask was already stored.
     * Different geometry for an overlapping mark needs the existing spatial
     * subtraction/protection adapter and is deliberately not guessed here. */
    fun addDiagonal(delta: DiagonalDelta): List<DiagonalDelta>? {
        m.cancellation.checkpoint()
        if (!RuntimeDataDomain.initial(delta.initialShape) || !RuntimeDataDomain.base(delta.base)) return emptyList()
        require(delta.initialShape.manager === m) { "A diagonal packet must use this AP manager" }
        val header = Header(delta.initialShape, delta.base, delta.layer, delta.tail, delta.exclusion)
        // A different tail/E header can already cover some offered atoms.
        // Keep packet admission atomic and use the exact scalar adapter below.
        if (hasOtherHeader(header, delta.marks)) return null
        val previous = findRows(header)
        if (previous != null) for ((shape, masks) in previous) {
            m.cancellation.checkpoint()
            if (!(masks.marks intersect delta.marks).isEmpty && shape != delta.geometry) return null
        }
        val old = previous?.get(delta.geometry)
        val stored = if (delta.protected) old?.protected else old?.plain
        val fresh = m.intern(delta.marks - (stored ?: MarkSet.EMPTY))
        if (fresh.isEmpty) return emptyList()
        val rows = previous ?: rowsFor(header)
        admit(rows, delta.geometry, if (delta.protected) MarkSet.EMPTY else fresh,
            if (delta.protected) fresh else MarkSet.EMPTY)
        return listOf(delta.copy(marks = fresh))
    }

    fun supports(premise: PremiseKey, facts: Facts): Boolean {
        m.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(premise, facts)) return false
        val f = facts as? TaintTree ?: return false
        if ((f.anyTail != Tail.STAR && f.anyTail != Tail.ANY) ||
            flowInitialForCoverage(m, premise) == null) return false
        val mark = ((premise as InitialAp).mark as MarkSlot.Concrete).mark
        val all = m.taintAlg.foldAll(f.root, m.cancellation)
        if (!all.exact.isEmpty || all.any != m.markSetOf(mark)) return false
        val flags = f.nonSubsumable?.let { m.taintAlg.foldAll(it, m.cancellation) }
        return flags == null || (flags.exact.isEmpty && flags.any.isSubsetOf(all.any))
    }

    /** Scalar adapter preserves each class while retaining shared mark masks. */
    fun add(premise: PremiseKey, facts: Facts): Facts? = addAll(premise, facts).let {
        check(it.size <= 1) { "Diagonal admission produced multiple packets; use addAll" }
        it.singleOrNull()
    }

    fun addAll(premise: PremiseKey, facts: Facts): List<Facts> {
        if (!RuntimeDataDomain.packet(premise, facts)) return emptyList()
        require(supports(premise, facts))
        val initial = premise as InitialAp
        val mark = (initial.mark as MarkSlot.Concrete).mark
        val one = m.markSetOf(mark)
        val output = ArrayList<Facts>()
        for (part in facts.membershipPackets(m)) {
            val f = part as TaintTree
            val protected = f.protectionClass()
            val scope = Scope(checkNotNull(flowInitialForCoverage(m, premise)), f.base, f.layer)
            val temporary = TaintGroup(m, interners.taint)
            for ((header, rows) in scopedRows(scope)) {
                var root: FlowNode? = null
                for ((shape, masks) in rows) {
                    val selected = if (protected) masks.protected else masks.plain
                    if (mark in selected) root = union(root, shape)
                }
                root?.let { temporary.restoreCurrent(decode(header, it, mark, if (protected) it else null)) }
            }
            val fresh = temporary.addAll(f)
            if (fresh.isEmpty()) continue
            // Prepare the complete replacement before mutating shared rows.
            val retained = temporary.all().toList()
            for ((header, rows) in scopedRows(scope).toList()) {
                for ((shape, masks) in rows.entries.toList()) {
                    if (protected) masks.protected = m.intern(masks.protected - one)
                    else masks.plain = m.intern(masks.plain - one)
                    if (masks.marks.isEmpty) rows.remove(shape)
                }
                if (rows.isEmpty()) removeHeader(header)
            }
            for (value in retained) {
                val header = Header(scope, value.anyTail, value.exclusion)
                admit(rowsFor(header), geometry(value.root),
                    if (protected) MarkSet.EMPTY else one, if (protected) one else MarkSet.EMPTY)
            }
            output += fresh
        }
        return output
    }

    private fun hasOtherHeader(offered: Header, marks: MarkSet): Boolean {
        for ((header, rows) in scopedRows(offered.scope)) {
            if (header.tail == offered.tail && header.exclusion == offered.exclusion) continue
            for (masks in rows.values) if (!(masks.marks intersect marks).isEmpty) return true
        }
        return false
    }

    fun all(): Sequence<Pair<PremiseKey, Facts>> = sequence {
        for ((header, rows) in allRows()) for ((shape, masks) in rows) {
            for (protected in listOf(false, true)) {
                val selected = if (protected) masks.protected else masks.plain
                for (id in selected.ids) {
                    m.cancellation.checkpoint()
                    val mark = TaintMark(id)
                    yield(markedInitial(header.initial, mark) to decode(header, shape, mark,
                        if (protected) shape else null))
                }
            }
        }
    }

    fun borrow(premise: PremiseKey): Sequence<Facts> = sequence {
        val initial = premise as? InitialAp ?: return@sequence
        val mark = (initial.mark as? MarkSlot.Concrete)?.mark ?: return@sequence
        val flow = flowInitialForCoverage(m, initial) ?: return@sequence
        for (scope in headers.keys) {
            if (scope.initial !== flow) continue
            for ((header, rows) in scopedRows(scope)) for ((shape, masks) in rows) {
                if (mark in masks.plain) yield(decode(header, shape, mark, null))
                if (mark in masks.protected) yield(decode(header, shape, mark, shape))
            }
        }
    }

    /** Remove plain diagonal outputs covered by one complete typed FLOW row. */
    fun compact(flowInitial: InitialAp, flowFacts: FlowTree) {
        m.cancellation.checkpoint()
        if (!flowInitial.isFlow || (flowInitial.tail != Tail.STAR && flowInitial.tail != Tail.ANY) ||
            (flowFacts.tail != Tail.STAR && flowFacts.tail != Tail.ANY)) return
        for (layer in Layer.entries) {
            m.cancellation.checkpoint()
            if (flowFacts.layer == Layer.DEMAND && layer == Layer.NORMAL) continue
            val scope = Scope(flowInitial, flowFacts.base, layer)
            for ((header, rows) in scopedRows(scope).toList()) {
                if (header.tail != flowFacts.tail ||
                    (header.tail == Tail.STAR && !flowFacts.exclusion.isSubsetOf(flowInitial.exclusion.union(header.exclusion)))) continue
                for ((shape, masks) in rows.entries.toList()) {
                    m.cancellation.checkpoint()
                    val selected = m.intern(masks.plain - flowFacts.markExclusion)
                    if (selected.isEmpty) continue
                    val rest = subtract(shape, flowFacts.root, header.tail)
                    if (rest === shape || rest == shape) continue
                    removeMark(rows, shape, masks, selected)
                    if (rest != null) admit(rows, rest, selected, MarkSet.EMPTY)
                }
                if (rows.isEmpty()) removeHeader(header)
            }
        }
    }

    private fun markedInitial(flow: InitialAp, mark: TaintMark): InitialAp =
        m.initial(flow.base, flow.path, flow.tail, flow.exclusion, MarkSlot.Concrete(mark))

    private fun removeMark(rows: MutableMap<FlowNode, Masks>, shape: FlowNode, masks: Masks, marks: MarkSet) {
        masks.plain = m.intern(masks.plain - marks)
        if (masks.marks.isEmpty) rows.remove(shape)
    }

    private fun admit(rows: MutableMap<FlowNode, Masks>, geometry: FlowNode, plain: MarkSet, protected: MarkSet) {
        val shape = interners.flow.internIfRequired(geometry)
        val masks = rows[shape]
        if (masks == null) rows[shape] = Masks(m.intern(plain), m.intern(protected))
        else {
            masks.plain = m.intern(masks.plain + plain)
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

}
