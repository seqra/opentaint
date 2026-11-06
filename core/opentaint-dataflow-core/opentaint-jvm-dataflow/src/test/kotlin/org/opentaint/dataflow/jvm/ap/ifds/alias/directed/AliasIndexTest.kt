package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertContentEquals
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertSame
import kotlin.test.assertTrue

/**
 * The two indexes of IMPL §4.3 (written cells by origin, holders of `AllocNew(s)` of loop sites)
 * agree with a full scan of the state, and the retire that uses them gives the result of Lean
 * `retireE` (a full scan).
 */
class AliasIndexTest {

    private val fx = DirectedEngineFixture(symDepth = 3)
    private val tr = fx.transfer
    private val origins = fx.origins
    private val nodes = fx.nodes

    private val loop1 = fx.loopSite(100)
    private val loop2 = fx.loopSite(101)
    private val plain = fx.site(102)
    private val cellIds = listOf(fx.field("f"), fx.field("g"), ELEM_CELL)

    /** The indexes computed by a full scan, compared with the indexes of the state. */
    private fun assertIndexMatchesScan(st: AliasState) {
        val cells = HashMap<OriginId, MutableSet<CellId>>()
        st.forEachHeap { k, _ -> cells.getOrPut(heapKeyOrigin(k)) { mutableSetOf() }.add(heapKeyCell(k)) }
        assertEquals(cells.keys, st.index.writtenOrigins().toSet(), "written origins")
        for ((o, cs) in cells) {
            val indexed = st.index.writtenCells(o)
            assertContentEquals(cs.sorted().toIntArray(), indexed, "written cells of $o")
        }

        val vars = HashMap<OriginId, MutableSet<VarId>>()
        val keys = HashMap<OriginId, MutableSet<HeapKey>>()
        fun tracked(n: NodeId) = nodes.members(n).filter {
            origins.isAllocNew(it) && fx.tables.sites.isLoopSite(origins.site(it))
        }
        st.forEachVar { v, n -> for (o in tracked(n)) vars.getOrPut(o) { mutableSetOf() }.add(v) }
        st.forEachHeap { k, n -> for (o in tracked(n)) keys.getOrPut(o) { mutableSetOf() }.add(k) }
        assertEquals(vars.keys + keys.keys, st.index.heldOrigins().toSet(), "held origins")
        for (o in vars.keys + keys.keys) {
            val h = st.index.holders(o)
            assertContentEquals((vars[o] ?: emptySet()).sorted().toIntArray(), h.vars, "var holders of $o")
            assertContentEquals((keys[o] ?: emptySet()).sorted().toLongArray(), h.keys, "heap holders of $o")
        }
    }

    /** Lean `retireE` by a full scan of the maps. */
    private fun referenceRetire(st: AliasState, s: SiteId): Pair<Map<VarId, NodeId>, Map<HeapKey, NodeId>> {
        val nw = origins.allocNew(s)
        val old = origins.allocOld(s)
        val env = HashMap<VarId, NodeId>()
        st.forEachVar { v, n -> env[v] = nodes.rename(n, nw, old) }
        val heap = HashMap<HeapKey, NodeId>()
        st.forEachHeap { k, _ ->
            val o = heapKeyOrigin(k)
            val c = heapKeyCell(k)
            val ro = if (o == nw) old else o
            val value = if (ro == old) {
                nodes.union(tr.read(st, nw, c), tr.read(st, old, c))
            } else {
                tr.read(st, o, c)
            }
            val renamed = nodes.rename(value, nw, old)
            if (renamed != origins.defaultNode(ro, c)) heap[heapKey(ro, c)] = renamed
        }
        return env to heap
    }

    private fun assertRetireMatchesReference(st: AliasState, s: SiteId) {
        val (env, heap) = referenceRetire(st, s)
        val r = tr.retire(st, s)
        assertEquals(env, HashMap(r.env), "env after retire")
        assertEquals(heap, HashMap(r.heap), "heap after retire")
        assertIndexMatchesScan(r)
    }

    @Test
    fun `index follows a sequence of store join retire and kill`() {
        val x = fx.arg(0)
        val y = fx.arg(1)
        val n = fx.local(0)
        val a = fx.local(1)
        val f = cellIds[0]
        val g = cellIds[1]
        val s1 = fx.run(
            fx.assign(n, AliasValue.New(loop1)),
            fx.store(n, f, n),
            fx.store(x, f, n),
            fx.assign(a, n),
        )
        assertIndexMatchesScan(s1)
        val nw = origins.allocNew(loop1)
        assertContentEquals(intArrayOf(n.v, a.v).sorted().toIntArray(), s1.index.holders(nw).vars)
        assertEquals(2, s1.index.holders(nw).keys.size)

        val s2 = fx.run(fx.store(y, g, x), fx.astore(n, y))
        assertIndexMatchesScan(s2)
        val j = tr.join(s1, s2).state
        assertIndexMatchesScan(j)

        val r = fx.run(fx.assign(n, AliasValue.New(loop1)), from = j)
        assertIndexMatchesScan(r)
        assertEquals(listOf(n.v), r.index.holders(nw).vars.toList())
        assertEquals(0, r.index.holders(nw).keys.size)

        val k = tr.kill(r) { it == a.v }
        assertIndexMatchesScan(k)
        assertEquals(0, k.index.holders(nw).vars.size)

        val sets = fx.withSets(k, fx.node(nw), fx.node(nw, fx.argO(0)))
        assertIndexMatchesScan(sets)
        assertEquals(listOf(ETREE, EVAL), sets.index.holders(nw).vars.toList())
        assertRetireMatchesReference(sets, loop1)
    }

    @Test
    fun `retire of a state without the site shares the state`() {
        val st = fx.run(fx.store(fx.arg(0), cellIds[0], fx.arg(1)))
        assertSame(st, tr.retire(st, loop2))
    }

    @Test
    fun `retire needs a loop site`() {
        assertFailsWith<IllegalArgumentException> { tr.retire(AliasState.EMPTY, plain) }
    }

    @Test
    fun `a site gets the loop flag before its new origin exists`() {
        val s = fx.site(200)
        origins.allocNew(s)
        assertFailsWith<IllegalStateException> { fx.tables.sites.markLoopSite(s) }
    }

    @Test
    fun `index and retire agree with a full scan on random programs`() {
        val locals = (0 until 5).map { fx.local(it) }
        val refs: List<AliasValue.Ref> = locals + listOf(fx.arg(0), fx.arg(1), AliasValue.This)
        val allocSites = listOf(loop1, loop2, plain)
        for (seed in 0 until 40) {
            val rnd = Random(seed)
            val history = ArrayList<AliasState>()
            var st = AliasState.EMPTY
            repeat(60) {
                val dst = locals.random(rnd)
                val ref = refs.random(rnd)
                val cell = cellIds.random(rnd)
                st = when (rnd.nextInt(9)) {
                    0, 1 -> tr.transfer(st, fx.assign(dst, AliasValue.New(allocSites.random(rnd))))
                    2 -> tr.transfer(st, fx.assign(dst, ref))
                    3 -> tr.transfer(st, AliasInstr.FieldLoad(dst.v, ref, cell))
                    4 -> tr.transfer(st, AliasInstr.FieldStore(ref, cell, refs.random(rnd)))
                    5 -> tr.transfer(st, AliasInstr.ArrayStore(ref, AliasValue.Null(fx.site(300 + it))))
                    6 -> if (history.isEmpty()) st else tr.join(st, history.random(rnd)).state
                    7 -> tr.kill(st) { v -> v != dst.v }
                    else -> fx.withSets(
                        st,
                        tr.load(st, tr.valueNode(st, ref), cell),
                        nodes.union(st.varNode(EVAL), tr.valueNode(st, ref)),
                    )
                }
                assertIndexMatchesScan(st)
                for (s in listOf(loop1, loop2)) assertRetireMatchesReference(st, s)
                history += st
            }
        }
        assertTrue(nodes.nodeCount > 1)
    }
}
