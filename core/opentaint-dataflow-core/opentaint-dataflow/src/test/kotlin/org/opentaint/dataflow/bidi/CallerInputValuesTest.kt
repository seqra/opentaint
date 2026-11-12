package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

/** The unchanged native accumulator is the oracle, including fresh headers and H. */
class CallerInputValuesTest {
    private val f = StoreFixtures()
    private val m = f.manager
    private val x = AccessPathBase.Argument(0)
    private val q = AccessPathBase.Return
    private val a = f.field("f")
    private val b = f.field("g")
    private val t = f.mark("T")
    private val u = f.mark("U")
    private val v = f.mark("V")
    private fun ref(source: TaintMark, stage: Int = 0, path: List<Int> = emptyList(),
                    e: ExclusionSet = ExclusionSet.Empty, tail: Tail = Tail.STAR) =
        CallerRef(f.key("caller"), m.initial(x, m.path(path), tail, e, MarkSlot.Concrete(source)),
            Layer.NORMAL, f.inst(1), stage)
    private fun fact(target: TaintMark, path: List<Int> = emptyList(), tail: Tail = Tail.EXACT,
                     e: ExclusionSet = ExclusionSet.Empty, layer: Layer = Layer.NORMAL,
                     protected: Boolean = false): TaintTree {
        val value = f.fact(q, path, tail, MarkSlot.Concrete(target), e, layer) as TaintTree
        return if (protected) value.withProtection(value.root) else value
    }
    private fun union(vararg values: TaintTree): TaintTree {
        val head = values.first()
        var root = head.root
        for (value in values.drop(1)) root = m.taintAlg.mergeAdd(root, value.root, m.cancellation)
        return m.taintTree(head.base, head.layer, root, head.exclusion, head.anyTail,
            if (head.nonSubsumable == null) null else root)
    }
    private fun compare(packed: CallerInputValues, scalar: AddedFactAccumulator,
                        ref: CallerRef, value: Facts): Int? {
        val old = scalar.add(ref, value.layer, value)
        val new = packed.add(ref, value.layer, value)
        assertEquals(old == null, new == null)
        if (old == null || new == null) return null
        assertEquals(old.handle, new.handle)
        assertEquals(old.newGroup, new.newGroup)
        assertEquals(old.delta, new.delta)
        assertEquals(old.snapshot, new.snapshot)
        assertEquals(scalar.size, packed.size)
        repeat(scalar.size) { assertEquals(scalar.snapshot(it), packed.snapshot(it), "handle=$it") }
        return new.handle
    }

    @Test fun `every offer preserves native snapshots and deltas for diagonal and changing packets`() {
        for (reverse in listOf(false, true)) {
            val packed = CallerInputValues(m, MarkMode.FULL)
            val scalar = AddedFactAccumulator(m)
            val refs = listOf(ref(t), ref(u), ref(v))
            val offers = listOf(
                refs[0] to fact(t, listOf(a)),
                refs[1] to fact(u, listOf(a)),
                refs[0] to union(fact(t, listOf(a)), fact(u, listOf(b))),
                refs[2] to union(fact(u, listOf(a)), fact(t, listOf(b))),
                refs[1] to union(fact(v, listOf(a)), fact(t, listOf(a)), fact(u, listOf(b))),
                refs[0] to fact(v, listOf(a, b)),
            ).let { if (reverse) it.reversed() else it }
            for ((r, offer) in offers + offers) compare(packed, scalar, r, offer)
            assertEquals(1, packed.packedFamilyCount)
            assertEquals(3, packed.packedSourceCount)
            assertEquals(0, packed.scalarCount)
            packed.clear()
            assertEquals(0, packed.size)
            assertEquals(0, packed.packedFamilyCount)
        }
    }

    @Test fun `packing keeps original admitted headers when a fresh exact delta clears E`() {
        val packed = CallerInputValues(m, MarkMode.FULL)
        val scalar = AddedFactAccumulator(m)
        val e = ExclusionSet.of(b)
        val r = ref(t)
        val must = fact(t, tail = Tail.ANY_TAINT, e = e)
        val handle = assertNotNull(compare(packed, scalar, r, must))
        val exact = fact(u, listOf(a))
        compare(packed, scalar, r, union(must, exact))
        assertEquals(e, packed.snapshot(handle).group.exclusion)
        assertEquals(e, (packed.snapshot(handle).facts as TaintTree).exclusion)
        compare(packed, scalar, r, exact)
        assertEquals(2, packed.size, "The Empty-E original header remains a different native key")
    }

    @Test fun `literal protection layers caller geometry and scope never share a family`() {
        val packed = CallerInputValues(m, MarkMode.FULL)
        val scalar = AddedFactAccumulator(m)
        val variants = listOf(
            ref(t) to fact(t),
            ref(u) to fact(u),
            ref(t) to fact(t, protected = true),
            ref(t) to fact(t, layer = Layer.DEMAND),
            ref(t, stage = 1) to fact(t),
            ref(t, path = listOf(a)) to fact(t),
            ref(t, e = ExclusionSet.of(b)) to fact(t),
            ref(t, tail = Tail.EXACT) to fact(t),
            ref(t).copy(callerLayer = Layer.DEMAND) to fact(t),
            ref(t).copy(call = f.inst(2)) to fact(t),
            ref(t).copy(caller = f.key("other")) to fact(t),
        )
        for ((r, value) in variants) compare(packed, scalar, r, value)
        assertEquals(variants.size - 1, packed.packedFamilyCount)
        assertEquals(0, packed.scalarCount)
    }

    @Test fun `group unsupported and non-singleton inputs stay scalar`() {
        val group = m.marks.group(m.marks.groupOf(t))
        val cases = listOf(
            ref(group) to fact(group),
            ref(t) to fact(group),
            ref(t).copy(premise = m.zero) to fact(t),
            ref(t).copy(premise = m.premiseOf(listOf(ref(t).premise.member(0), ref(u).premise.member(0)))) to fact(t),
            ref(t).copy(premise = m.initial(x, null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR)) to
                f.fact(q, tail = Tail.STAR, mark = MarkSlot.STAR),
            ref(t).copy(premise = m.zero) to Reach.NORMAL,
        )
        for (mode in MarkMode.entries) {
            val packed = CallerInputValues(m, mode)
            val scalar = AddedFactAccumulator(m)
            for ((r, value) in cases) compare(packed, scalar, r, value)
            assertEquals(cases.size, packed.scalarCount)
            assertEquals(0, packed.packedFamilyCount)
        }
    }

    @Test fun `fallback migrates only one source and retains its logical handle and other packed sources`() {
        val packed = CallerInputValues(m, MarkMode.FULL)
        val scalar = AddedFactAccumulator(m)
        val handleT = assertNotNull(compare(packed, scalar, ref(t), fact(t, listOf(a))))
        val handleU = assertNotNull(compare(packed, scalar, ref(u), fact(u, listOf(a))))
        val beforeU = packed.snapshot(handleU)
        val group = m.marks.group(m.marks.groupOf(t))
        assertEquals(handleT, compare(packed, scalar, ref(t), fact(group, listOf(b))))
        assertEquals(beforeU, packed.snapshot(handleU))
        assertEquals(1, packed.packedSourceCount)
        assertEquals(1, packed.scalarCount)
        compare(packed, scalar, ref(t), fact(v, listOf(a, b)))
        compare(packed, scalar, ref(u), fact(t, listOf(b)))
        assertEquals(1, packed.scalarCount, "A migrated slot never creates a second packed authority")
        assertEquals(1, packed.packedSourceCount)
    }

    @Test fun `all small changing relations decode without a cartesian product`() {
        val marks = listOf(t, u, v)
        repeat(512) { mask ->
            val packed = CallerInputValues(m, MarkMode.FULL)
            val scalar = AddedFactAccumulator(m)
            for ((sourceIndex, source) in marks.withIndex()) for ((targetIndex, target) in marks.withIndex()) {
                if (mask and (1 shl (sourceIndex * 3 + targetIndex)) != 0)
                    compare(packed, scalar, ref(source), fact(target, listOf(a)))
            }
        }
    }

    @Test fun `snapshot is immutable after later growth and packing walks deep paths without recursion`() {
        val packed = CallerInputValues(m, MarkMode.FULL)
        val scalar = AddedFactAccumulator(m)
        val deep = List(4096) { a }
        val h = assertNotNull(compare(packed, scalar, ref(t), fact(t, deep)))
        val before = packed.snapshot(h)
        compare(packed, scalar, ref(t), fact(u, listOf(b)))
        assertEquals(1, f.ops.leaves(before.facts).count())
        assertEquals(2, f.ops.leaves(packed.snapshot(h).facts).count())
        f.cancellation.cancel()
        assertFails { packed.snapshot(h) }
        assertFails { packed.add(ref(t), Layer.NORMAL, fact(t)) }
    }

    @Test fun `noncanonical exact-only native headers keep the unchanged scalar representation`() {
        for (tail in listOf(Tail.STAR, Tail.ANY)) for (protected in listOf(false, true)) {
            val packed = CallerInputValues(m, MarkMode.FULL)
            val scalar = AddedFactAccumulator(m)
            val exact = fact(t, layer = Layer.DEMAND, protected = protected)
            // The internal constructor accepts this shape; the canonical factory rewrites its tail.
            val offered = TaintTree(exact.base, exact.layer, exact.root, anyTail = tail,
                nonSubsumable = exact.nonSubsumable)
            compare(packed, scalar, ref(t), offered)
            assertEquals(1, packed.scalarCount)
            assertEquals(0, packed.packedSourceCount)
            compare(packed, scalar, ref(t), offered)
        }
    }

    @Test fun `an unsupported exact-only offer migrates a packed STAR group without changing another source`() {
        val packed = CallerInputValues(m, MarkMode.FULL)
        val scalar = AddedFactAccumulator(m)
        compare(packed, scalar, ref(t), fact(t, tail = Tail.STAR))
        val other = assertNotNull(compare(packed, scalar, ref(u), fact(u, tail = Tail.STAR)))
        val before = packed.snapshot(other)
        val exact = fact(v, listOf(a))
        val raw = TaintTree(exact.base, exact.layer, exact.root, anyTail = Tail.STAR)
        compare(packed, scalar, ref(t), raw)
        assertEquals(before, packed.snapshot(other))
        assertEquals(1, packed.scalarCount)
        assertEquals(1, packed.packedSourceCount)
    }

    @Test fun `output coordinates do not enter the shared strong premise path interner`() {
        val packed = CallerInputValues(m, MarkMode.FULL)
        val r = ref(t)
        var root = m.taintAlg.leafNode(m.taintLeaves(m.markSetOf(u), MarkSet.EMPTY))
        repeat(128) { root = m.taintAlg.node(TaintLeaves.EMPTY, intArrayOf(a), arrayOf(root)) }
        val offered = m.taintTree(q, Layer.NORMAL, root)
        val field = ApManager::class.java.getDeclaredField("paths").also { it.isAccessible = true }
        val sharedPaths = field.get(m) as Map<*, *>
        val before = sharedPaths.size
        val added = assertNotNull(packed.add(r, offered.layer, offered))
        assertEquals(offered, packed.snapshot(added.handle).facts)
        packed.clear()
        assertEquals(before, sharedPaths.size, "Directory output paths must be released with their owner")
    }
}
