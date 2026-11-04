package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class LocalInputCandidateTest {
    private val f = StoreFixtures()
    private val ap = f.manager
    private val ops = f.ops
    private val x = AccessPathBase.Argument(0)
    private val y = AccessPathBase.Argument(1)
    private val a = f.field("a")
    private val b = f.field("b")
    private val t = MarkSlot.Concrete(f.mark("T"))
    private val parent = BlockScope(BlockId(1), PortId(1))
    private val child = BlockScope(BlockId(2), PortId(2))
    private val mode = ApMode(false, Direction.FORWARD, 5)

    private fun add(directory: LocalInputDirectory, facts: Facts, ordinal: Int, original: PremiseKey? = null): LocalInputValue {
        val p = original ?: ap.initial(f.pattern(facts.base, mark = t))
        val link = LocalLink(parent, PortId(10 + ordinal), p, facts.layer, child)
        val value = LocalInputValue(link, facts)
        val key = LocalInputKey(link, facts.groupKey)
        directory[key] = value
        directory.recordDelta(key, facts)
        return value
    }

    @Test fun `inverse lookup omits unrelated input positions and preserves native matches`() {
        val directory = LocalInputDirectory(ops)
        val kept = add(directory, f.fact(x, listOf(a, b), mark = t), 0)
        add(directory, f.fact(x, listOf(b), mark = t), 1)
        add(directory, f.fact(y, listOf(a), mark = t), 2)
        val initial = ap.initial(f.pattern(x, listOf(a), Tail.STAR, MarkSlot.STAR))
        val selected = directory.candidates(initial, mode)
        assertEquals(listOf(kept), selected.map { it.input }, "Unrelated inputs must not reach the full matcher")
        val native = directory.values.filter { ops.satisfying(it.value, initial, mode) != null }
        assertEquals(native, selected.filter { ops.satisfying(it.input.value, initial, mode) != null }.map { it.input })
    }

    @Test fun `ND candidates keep input insertion then member order and exact duplicate suppression`() {
        val directory = LocalInputDirectory(ops)
        val iy = ap.initial(f.pattern(y, mark = t))
        val ix = ap.initial(f.pattern(x, mark = t))
        val row = ap.union(ix, iy)
        add(directory, f.fact(y, mark = t), 0)
        val packed = ap.mergeAddDelta(f.fact(x, mark = t), f.fact(x, listOf(a), mark = t)).first
        add(directory, packed, 1)
        val expected = directory.values.flatMap { input -> (0 until row.size).mapNotNull { member ->
            if (ops.satisfying(input.value, row.member(member), mode) != null) LocalInputCandidate(input, member) else null
        } }
        val candidates = directory.candidates(row, mode)
        val matched = candidates.filter { ops.satisfying(it.input.value, row.member(it.member), mode) != null }
        assertEquals(expected, matched)
        assertEquals(candidates.size, candidates.toSet().size)
    }

    @Test fun `run1 certified static control is separate from ordinary Reach candidates`() {
        val directory = LocalInputDirectory(ops)
        val zero = add(directory, Reach.NORMAL, 0, ap.zero)
        add(directory, Reach.NORMAL, 1, ap.initial(f.pattern(x, mark = t)))
        val clazz = ap.accessors.index(ClassStaticAccessor("C"))
        val static = ap.initial(f.pattern(STATIC, listOf(clazz, a), Tail.STAR, MarkSlot.STAR))
        assertEquals(listOf(zero), directory.candidates(static, ApMode(true, Direction.FORWARD, 1)).map { it.input })
        assertTrue(directory.candidates(static, mode).isEmpty())
        assertEquals(2, directory.candidates(ap.zero, mode).size, "Ordinary ZERO matches all Reach originals")
    }
}
