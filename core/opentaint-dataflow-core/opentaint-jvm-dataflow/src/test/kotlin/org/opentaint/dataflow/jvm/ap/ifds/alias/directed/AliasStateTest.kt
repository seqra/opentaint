package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotEquals
import kotlin.test.assertSame
import kotlin.test.assertTrue

class AliasStateTest {

    private val fx = DirectedEngineFixture()
    private val f = fx.field("f")
    private val g = fx.field("g")
    private val x = fx.arg(0)
    private val z = fx.arg(2)
    private val a = fx.local(0)
    private val t = fx.local(1)

    @Test
    fun `this and arguments have their root by rule and are not in env`() {
        val st = AliasState.EMPTY
        assertEquals(fx.set(fx.argO(0)), fx.pts(st, x))
        assertEquals(fx.set(fx.thisO()), fx.pts(st, AliasValue.This))
        assertEquals(0, st.env.size)
    }

    @Test
    fun `reserved keys are absent at entry and read as the empty set`() {
        val st = AliasState.EMPTY
        assertEquals(EMPTY_NODE, st.varNode(ETREE))
        assertEquals(EMPTY_NODE, st.varNode(EVAL))
        assertFalse(st.env.containsKey(ETREE))
    }

    @Test
    fun `env has no entry for the empty set`() {
        val st = AliasState.EMPTY.edit().apply { setVar(fx.tables.vars.local(0), EMPTY_NODE) }.build()
        assertEquals(0, st.env.size)
        // A copy of an unassigned local gives no entry.
        val st2 = fx.run(fx.assign(a, t))
        assertEquals(0, st2.env.size)
    }

    @Test
    fun `put removes a key whose node is the default`() {
        val xo = fx.argO(0)
        val st1 = fx.transfer.put(AliasState.EMPTY, xo, f, fx.node(fx.argO(2)))
        assertTrue(st1.isWritten(heapKey(xo, f)))
        val st2 = fx.transfer.put(st1, xo, f, fx.origins.defaultNode(xo, f))
        assertFalse(st2.isWritten(heapKey(xo, f)))
        assertEquals(AliasState.EMPTY, st2)
    }

    @Test
    fun `a strong store of the old content gives the state without the store`() {
        // t = x.f; x.f = z; x.f = t   gives the state of   t = x.f
        val st1 = fx.run(fx.load(t, x, f), fx.store(x, f, z), fx.store(x, f, t))
        val st2 = fx.run(fx.load(t, x, f))
        assertEquals(0, st1.heap.size)
        assertEquals(st2, st1)
        assertEquals(st2.hashCode(), st1.hashCode())
    }

    @Test
    fun `map equality is state equality in normal form`() {
        // Two orders of two weak stores give equal maps.
        val ab = fx.transfer.join(fx.run(fx.assign(a, x)), fx.run(fx.assign(a, z))).state
        val one = fx.run(fx.store(a, f, z), fx.store(a, g, x), from = ab)
        val two = fx.run(fx.store(a, g, x), fx.store(a, f, z), from = ab)
        assertEquals(one, two)

        // Different content gives different states.
        val three = fx.run(fx.store(a, g, x), from = ab)
        assertNotEquals(one, three)

        // An assigned variable makes a different state.
        assertNotEquals(fx.run(fx.assign(a, x)), AliasState.EMPTY)
    }

    @Test
    fun `an instruction that changes nothing shares the state`() {
        val st = fx.run(fx.assign(a, x))
        assertSame(st, fx.transfer.transfer(st, AliasInstr.Nop))
        assertSame(st, fx.transfer.transfer(st, AliasInstr.StaticWrite))
        assertSame(st, fx.transfer.transfer(st, AliasInstr.Throw(a)))
        assertSame(st, fx.transfer.transfer(st, AliasInstr.Return(a)))
        assertSame(st, fx.transfer.transfer(st, AliasInstr.Return(null)))
        // A copy of the same node shares the state.
        assertSame(st, fx.transfer.transfer(st, fx.assign(a, x)))
    }

    @Test
    fun `copy on write does not change the input state`() {
        val st = fx.run(fx.assign(a, x))
        val before = AliasState(st.env.clone(), st.heap.clone())
        fx.run(fx.store(a, f, z), fx.assign(a, z), from = st)
        assertEquals(before, st)
    }

    @Test
    fun `kill removes dead locals and keeps the reserved keys`() {
        val etree = fx.node(fx.argO(0))
        val st = fx.withSets(fx.run(fx.assign(a, x), fx.assign(t, z)), etree, etree)
        val killed = fx.transfer.kill(st) { it == t.v }
        assertEquals(EMPTY_NODE, killed.varNode(a.v))
        assertEquals(fx.set(fx.argO(2)), fx.pts(killed, t))
        assertEquals(etree, killed.varNode(ETREE))
        assertEquals(etree, killed.varNode(EVAL))
        assertSame(killed, fx.transfer.kill(killed) { it == t.v })
    }

    @Test
    fun `written heap entries can be iterated`() {
        val st = fx.run(fx.store(x, f, z), fx.store(z, g, x))
        val keys = mutableSetOf<HeapKey>()
        st.forEachHeap { k, _ -> keys += k }
        assertEquals(setOf(heapKey(fx.argO(0), f), heapKey(fx.argO(2), g)), keys)
        val cells = st.index.writtenCells(fx.argO(0))
        assertEquals(listOf(f), cells.toList())
        assertEquals(0, st.index.writtenCells(fx.argO(1)).size)
    }
}
