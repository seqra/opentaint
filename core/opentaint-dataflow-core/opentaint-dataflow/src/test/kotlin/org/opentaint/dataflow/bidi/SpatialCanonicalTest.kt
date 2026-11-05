package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import kotlin.test.*

/** Selected spatial laws: literal headers and paths, rather than only counts. */
class SpatialCanonicalTest {
    private val f = StoreFixtures()
    private val m = f.manager
    private val x = AccessPathBase.Argument(0)
    private val a = f.field("a")
    private val b = f.field("b")
    private val c = f.field("c")
    private val t = f.mark("T")
    private val u = f.mark("U")
    private fun e(vararg fields: Int) = ExclusionSet.of(fields)
    private fun flow(vararg paths: List<Int>, tail: Tail = Tail.ANY_TAINT,
                     excluded: ExclusionSet = ExclusionSet.Empty, mx: MarkSet = MarkSet.EMPTY,
                     layer: Layer = if (tail == Tail.ANY) Layer.DEMAND else Layer.NORMAL): FlowTree =
        m.flowTree(x, layer, excluded, mx,
            paths.map { FlowAlgebra.prepend(m, m.path(it), FlowAlgebra.LEAF_NODE) }
                .reduce { left, right -> FlowAlgebra.mergeAdd(left, right) }, tail)
    private fun taint(vararg paths: Pair<List<Int>, MarkSet>, tail: Tail = Tail.ANY_TAINT,
                      excluded: ExclusionSet = ExclusionSet.Empty,
                      layer: Layer = if (tail == Tail.ANY) Layer.DEMAND else Layer.NORMAL): TaintTree =
        m.taintTree(x, layer, paths.map { (path, marks) ->
            m.taintAlg.prepend(m, m.path(path), m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY, marks)))
        }.reduce { left, right -> m.taintAlg.mergeAdd(left, right) }, excluded, tail)
    private fun one(mark: TaintMark = t) = m.markSetOf(mark)
    private fun leaves(values: Sequence<Facts>) = values.flatMap { f.ops.leaves(it) }.toSet()
    private fun expected(vararg values: Facts) = leaves(values.asSequence())

    @Test fun `FLOW one packet and both arrival orders remove same-tail descendants`() {
        for (tail in listOf(Tail.ANY, Tail.ANY_TAINT)) {
            val root = flow(emptyList(), tail = tail)
            val child = flow(listOf(a, b), tail = tail)
            for (packets in listOf(listOf(flow(emptyList(), listOf(a, b), tail = tail)),
                listOf(root, child), listOf(child, root))) {
                val group = FlowGroup(m, m.newInterners().flow)
                packets.forEach(group::addAll)
                assertEquals(expected(root), leaves(group.all()))
                assertNull(group.add(root))
            }
        }
    }

    @Test fun `TAINT one packet and broad-after-narrow prune each supported mark only`() {
        for (tail in listOf(Tail.ANY, Tail.ANY_TAINT)) {
            val root = taint(emptyList<Int>() to one(), tail = tail)
            val childT = taint(listOf(a) to one(), tail = tail)
            val childU = taint(listOf(a) to one(u), tail = tail)
            for (packets in listOf(listOf(taint(emptyList<Int>() to one(), listOf(a) to (one() + one(u)), tail = tail)),
                listOf(childT, childU, root), listOf(root, childT, childU))) {
                val group = TaintGroup(m, m.newInterners().taint)
                packets.forEach(group::addAll)
                assertEquals(expected(root, childU), leaves(group.all()))
            }
        }
    }

    @Test fun `MUST proper descendant coverage ignores the descendant exclusion`() {
        val root = flow(emptyList(), excluded = e(a))
        val admitted = flow(listOf(b), excluded = e(c))
        val blocked = flow(listOf(a, b), excluded = e(c))
        for (order in listOf(listOf(root, admitted, blocked), listOf(admitted, blocked, root))) {
            val group = FlowGroup(m, m.newInterners().flow)
            order.forEach(group::addAll)
            assertEquals(expected(root, blocked), leaves(group.all()))
        }
    }

    @Test fun `complete immediate MUST child fills its hole in either order`() {
        val root = flow(emptyList(), excluded = e(a, b))
        val child = flow(listOf(a))
        for (order in listOf(listOf(root, child), listOf(child, root))) {
            val group = FlowGroup(m, m.newInterners().flow)
            order.forEach(group::addAll)
            assertEquals(expected(flow(emptyList(), excluded = e(b))), leaves(group.all()))
        }
    }

    @Test fun `long child and excluded child cannot fill a MUST hole`() {
        val root = flow(emptyList(), excluded = e(a))
        for (child in listOf(flow(listOf(a, b)), flow(listOf(a), excluded = e(b)))) {
            val group = FlowGroup(m, m.newInterners().flow)
            group.add(root); group.add(child)
            assertEquals(expected(root, child), leaves(group.all()))
        }
    }

    @Test fun `complete bottom-up fill can complete its parent`() {
        val root = flow(emptyList(), excluded = e(a))
        val child = flow(listOf(a), excluded = e(b))
        val grandchild = flow(listOf(a, b))
        for (order in listOf(listOf(root, child, grandchild), listOf(grandchild, child, root))) {
            val group = FlowGroup(m, m.newInterners().flow)
            order.forEach(group::addAll)
            assertEquals(expected(flow(emptyList())), leaves(group.all()))
        }
    }

    @Test fun `concrete partial-mark fill keeps the other mark hole`() {
        val group = TaintGroup(m, m.newInterners().taint)
        group.add(taint(emptyList<Int>() to (one() + one(u)), excluded = e(a)))
        group.add(taint(listOf(a) to one()))
        assertEquals(expected(taint(emptyList<Int>() to one()),
            taint(emptyList<Int>() to one(u), excluded = e(a))), leaves(group.all()))
    }

    @Test fun `one incoming packet can strengthen two distinct exclusion headers`() {
        val group = TaintGroup(m, m.newInterners().taint)
        group.add(taint(emptyList<Int>() to (one() + one(u)), excluded = e(a,b)))
        // The new addAll API must return both strengthened canonical roots.
        val changed = group.addAll(taint(listOf(a) to one(), listOf(b) to one(u)))
        assertEquals(2, changed.size)
        assertEquals(expected(taint(emptyList<Int>() to one(), excluded = e(b)),
            taint(emptyList<Int>() to one(u), excluded = e(a))), leaves(group.all()))
    }

    @Test fun `narrower FLOW mark support cannot fill a parent hole`() {
        val group = FlowGroup(m, m.newInterners().flow)
        val root = flow(emptyList(), excluded = e(a))
        val child = flow(listOf(a), mx = one())
        group.add(root); group.add(child)
        assertEquals(expected(root,child), leaves(group.all()))
    }

    @Test fun `FLOW child with broader mark support fills parent and retains extra support`() {
        val group = FlowGroup(m, m.newInterners().flow)
        group.add(flow(emptyList(), excluded = e(a), mx = one()))
        group.addAll(flow(listOf(a)))
        assertEquals(expected(flow(emptyList(), mx = one()), flow(listOf(a))), leaves(group.all()))
    }

    @Test fun `coordinatewise cofinite union supplies a complete MUST child without changing siblings`() {
        val root = flow(emptyList(),excluded = e(a,b,c))
        val left = flow(listOf(a),listOf(b),mx = one())
        val right = flow(listOf(a),listOf(c),mx = one(u))
        val paths = listOf(emptyList(),listOf(a),listOf(a,a),listOf(a,b),listOf(b),listOf(b,a),listOf(c),listOf(c,b))
        val marks = listOf(t,u,f.mark("V"))
        fun region(values: List<FlowTree>): Set<Pair<List<Int>,TaintMark>> = buildSet {
            for (value in values) for (leaf in f.ops.leaves(value)) for (path in paths) for (mark in marks) {
                val prefix = leaf.fact.path
                if (mark in (leaf.fact.mark as MarkSlot.Star).excluded || path.size < prefix.size ||
                    path.take(prefix.size) != prefix) continue
                if (path.size == prefix.size || value.exclusion.admits(path[prefix.size])) add(path to mark)
            }
        }
        for (order in listOf(listOf(root,left,right),listOf(right,left,root),listOf(root,right,left))) {
            val group = FlowGroup(m,m.newInterners().flow)
            val changes = ArrayList<FlowTree>()
            for (value in order) changes.addAll(group.addAll(value))
            val current = group.all().toList()
            assertEquals(expected(flow(emptyList(),excluded = e(b,c)),flow(listOf(b),mx = one()),
                flow(listOf(c),mx = one(u))),leaves(current.asSequence()))
            assertEquals(region(order),region(current))
            assertEquals(region(current),region(changes))
        }
    }

    @Test fun `shared-coordinate cofinite join cannot fill with the same missing mark`() {
        val group = FlowGroup(m,m.newInterners().flow)
        group.addAll(flow(emptyList(),excluded = e(a,b,c)))
        group.addAll(flow(listOf(a),listOf(b),mx = one()))
        group.addAll(flow(listOf(a),listOf(c),mx = one()))
        assertEquals(expected(flow(emptyList(),excluded = e(a,b,c)),
            flow(listOf(a),listOf(b),listOf(c),mx = one())),leaves(group.all()))
    }

    @Test fun `plain ancestor preserves protected child and does not fabricate protection`() {
        val group = TaintGroup(m, m.newInterners().taint)
        val protected = taint(listOf(a) to one()).let { it.withProtection(it.root) }
        group.add(protected)
        group.add(taint(emptyList<Int>() to one()))
        assertEquals(expected(protected), leaves(group.all().mapNotNull { it.protectedPart() }))
        assertEquals(expected(taint(emptyList<Int>() to one()), protected), leaves(group.all()))
    }

    @Test fun `ordinary E intersection cannot weaken one-sided protected E`() {
        val first = taint(listOf(a) to one(),listOf(b) to one(u),excluded = e(a))
        val flags = taint(listOf(a) to one(),excluded = e(a))
        val protected = first.withProtection(flags.root)
        val second = taint(listOf(a) to one(),listOf(b) to one(u),excluded = e(b))
        for (order in listOf(listOf(protected,second),listOf(second,protected))) {
            val group = TaintGroup(m,m.newInterners().taint)
            order.forEach(group::addAll)
            assertEquals(expected(flags),leaves(group.all().mapNotNull { it.protectedPart() }))
        }
    }

    @Test fun `shared DAG leaf keeps separate inherited exclusion coverage`() {
        val shared = m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY,one()))
        val root = m.taintAlg.node(shared.leaf,intArrayOf(a,b),arrayOf(shared,shared))
        val packet = m.taintTree(x,Layer.NORMAL,root,e(a),Tail.ANY_TAINT)
        val canonical = m.canonicalPackets(packet)
        assertEquals(expected(taint(emptyList<Int>() to one(),listOf(a) to one(),excluded = e(a))),
            leaves(canonical.asSequence()))
        assertSame(shared,assertIs<TaintTree>(canonical.single()).root.child(a))
        assertNull(assertIs<TaintTree>(canonical.single()).root.child(b))
    }

    @Test fun `packed exponential MAY geometry is normalized without path enumeration`() {
        var root = FlowAlgebra.LEAF_NODE
        repeat(20) { root = FlowAlgebra.node(FlowLeaf.NONE,intArrayOf(a,b),arrayOf(root,root)) }
        assertTrue(root.size > 1_000_000L)
        val packet = m.flowTree(x,Layer.DEMAND,ExclusionSet.Empty,MarkExclusions.EMPTY,root,Tail.ANY)
        val canonical = assertIs<FlowTree>(m.canonicalPackets(packet).single())
        assertSame(packet,canonical)
        assertSame(root,canonical.root)
    }

    @Test fun `MUST canonicalization does not consume exact or STAR cells or another layer`() {
        val group = ConclusionGroup(m, m.newInterners())
        val root = flow(emptyList())
        val exact = f.fact(x, listOf(a), Tail.EXACT)
        val star = flow(listOf(a), tail = Tail.STAR)
        val demand = flow(listOf(a), tail = Tail.ANY)
        listOf(root, exact, star, demand).forEach(group::add)
        assertEquals(expected(root,exact,star,demand), leaves(group.all()))
    }
}
