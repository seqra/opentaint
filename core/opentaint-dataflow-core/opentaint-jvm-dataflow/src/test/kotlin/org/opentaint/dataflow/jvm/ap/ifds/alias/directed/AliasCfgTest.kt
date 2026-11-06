package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.AliasCfg.Node
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/** Tests of the alias CFG of the direct builder: edges, cycles, loop sites, WTO, liveness (IMPL §5). */
class AliasCfgTest {

    private val fx = DirectedEngineFixture()
    private val f = fx.field("f")
    private val x = fx.local(0)
    private val y = fx.local(1)
    private val t = fx.local(2)

    private fun node(instr: AliasInstr, vararg succ: Int, exc: IntArray = intArrayOf()) = Node(instr, succ, exc)

    private fun cfg(vararg nodes: Node, entry: Int = 0, callOnCycle: Boolean = false): AliasCfg =
        AliasCfg.direct(fx.tables, nodes.toList(), entry = entry, callOnCycle = callOnCycle)

    private fun AliasCfg.live(v: Int): Set<VarId> = liveIn(v).stream().toArray().toSet()

    private fun WtoComponent.show(): String = when (this) {
        is WtoComponent.Vertex -> "$node"
        is WtoComponent.Loop -> "($head" + body.joinToString("") { " " + it.show() } + ")"
    }

    private fun AliasCfg.wtoText(): String = wto.joinToString(" ") { it.show() }

    @Test
    fun `exceptional edges give the throwers of a handler`() {
        val s1 = fx.site(1)
        val g = cfg(
            node(fx.assign(x, AliasValue.New(fx.site(0))), 1),
            node(AliasInstr.UnresolvedCall(s1, null, emptyList()), 2, exc = intArrayOf(3)),
            node(AliasInstr.Nop),
            node(AliasInstr.Assign(t.v, AliasValue.Fresh(fx.site(3))), 2),
        )
        assertEquals(listOf(1), g.throwers(3).toList())
        assertEquals(listOf(3), g.handlers(1).toList())
        assertEquals(emptyList(), g.normalPredecessors(3).toList())
        assertEquals(listOf(1, 3), g.normalPredecessors(2).toList().sorted())
    }

    @Test
    fun `a node on a cycle of either edge kind is a loop node and its site is a loop site`() {
        val s0 = fx.site(0)
        val s1 = fx.site(1)
        val s3 = fx.site(3)
        // The cycle 1 -> 3 -> 1 uses the exceptional edge 1 -> 3.
        val g = cfg(
            node(fx.assign(x, AliasValue.New(s0)), 1),
            node(AliasInstr.UnresolvedCall(s1, y.v, emptyList()), 2, exc = intArrayOf(3)),
            node(AliasInstr.Nop),
            node(fx.assign(t, AliasValue.New(s3)), 1),
        )
        assertFalse(g.onCycle(0))
        assertTrue(g.onCycle(1))
        assertFalse(g.onCycle(2))
        assertTrue(g.onCycle(3))
        assertFalse(fx.tables.sites.isLoopSite(s0))
        assertTrue(fx.tables.sites.isLoopSite(s1))
        assertTrue(fx.tables.sites.isLoopSite(s3))
    }

    @Test
    fun `a site at two nodes is a loop site`() {
        val s = fx.site(7)
        cfg(
            node(fx.assign(x, AliasValue.New(s)), 1),
            node(fx.assign(y, AliasValue.New(s))),
        )
        assertTrue(fx.tables.sites.isLoopSite(s))
    }

    @Test
    fun `each site of a callee is a loop site if the call is on a cycle of the caller`() {
        val s = fx.tables.sites.site(0, context = 1)
        cfg(node(AliasInstr.Assign(fx.tables.vars.local(0, 1), AliasValue.New(s))), callOnCycle = true)
        assertTrue(fx.tables.sites.isLoopSite(s))
    }

    @Test
    fun `wto puts the entry in a component when a back edge reaches it`() {
        val g = cfg(
            node(fx.load(t, x, f), 1),
            node(fx.store(x, f, y), 0, 2),
            node(AliasInstr.Return(t)),
        )
        assertEquals("(0 1) 2", g.wtoText())
    }

    @Test
    fun `wto of nested loops has the inner loop in the body of the outer loop`() {
        val g = cfg(
            node(AliasInstr.Nop, 1),
            node(AliasInstr.Nop, 2, 5),
            node(AliasInstr.Nop, 3),
            node(AliasInstr.Nop, 2, 4),
            node(AliasInstr.Nop, 1),
            node(AliasInstr.Nop),
        )
        assertEquals("0 (1 (2 3) 4) 5", g.wtoText())
    }

    @Test
    fun `wto of an irreducible cycle has one head`() {
        // 0 -> 1, 0 -> 2, 1 <-> 2: the cycle has two entries.
        val g = cfg(
            node(AliasInstr.Nop, 1, 2),
            node(AliasInstr.Nop, 2, 3),
            node(AliasInstr.Nop, 1, 3),
            node(AliasInstr.Nop),
        )
        assertEquals("0 (1 2) 3", g.wtoText())
    }

    @Test
    fun `wto has a component for a self loop and no node that the entry does not reach`() {
        val g = cfg(
            node(AliasInstr.Nop, 1),
            node(AliasInstr.Nop, 1, 2),
            node(AliasInstr.Nop),
            node(AliasInstr.Nop, 2),
        )
        assertEquals("0 (1) 2", g.wtoText())
        assertFalse(g.isReachable(3))
    }

    @Test
    fun `liveness of a variable ends at its last read`() {
        val g = cfg(
            node(fx.assign(x, AliasValue.New(fx.site(0))), 1),
            node(fx.assign(y, x), 2),
            node(AliasInstr.Return(y)),
        )
        assertEquals(emptySet(), g.live(0))
        assertEquals(setOf(x.v), g.live(1))
        assertEquals(setOf(y.v), g.live(2))
    }

    @Test
    fun `liveness keeps at a thrower each variable that its handler reads also the written one`() {
        // live_spec_unsound: 0: x = new; 1: y = x; 2: x = m() (handler 3); 3: x.f = y; 4: nop
        val g = cfg(
            node(fx.assign(x, AliasValue.New(fx.site(0))), 1),
            node(fx.assign(y, x), 2),
            node(AliasInstr.UnresolvedCall(fx.site(2), x.v, emptyList()), 4, exc = intArrayOf(3)),
            node(fx.store(x, f, y), 4),
            node(AliasInstr.Nop),
        )
        assertEquals(setOf(x.v, y.v), g.live(3))
        assertEquals(setOf(x.v, y.v), g.live(2))
        assertEquals(setOf(x.v), g.live(1))
    }

    @Test
    fun `liveness uses the extra reads of a node`() {
        val g = AliasCfg.direct(
            fx.tables,
            listOf(
                Node(fx.assign(x, AliasValue.New(fx.site(0))), intArrayOf(1)),
                Node(AliasInstr.Nop, intArrayOf(2), extraUses = intArrayOf(x.v)),
                Node(AliasInstr.Nop),
            ),
        )
        assertEquals(setOf(x.v), g.live(1))
    }
}
