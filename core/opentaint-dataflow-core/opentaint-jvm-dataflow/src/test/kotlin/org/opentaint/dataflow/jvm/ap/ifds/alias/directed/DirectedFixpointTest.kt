package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import org.opentaint.dataflow.ap.ifds.analysis.alias.AnalysisCancellation
import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.AliasCfg.Node
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue
import kotlin.time.Duration

/**
 * Tests of the WTO fixpoint on programs of the direct CFG builder (IMPL §5.1-§5.4). Each test
 * checks the post-fixpoint conditions of the final states ([PostFixChecker]).
 */
class DirectedFixpointTest {

    private val fx = DirectedEngineFixture()
    private val fp = DirectedFixpoint(fx.transfer)
    private val checker = PostFixChecker(fp)
    private val origins = fx.origins
    private val bases = fx.bases
    private val f = fx.field("f")
    private val next = fx.field("next")

    private val x = fx.local(0)
    private val y = fx.local(1)
    private val t = fx.local(2)
    private val a = fx.local(3)
    private val e = fx.local(4)
    private val n = fx.local(5)
    private val cur = fx.local(6)
    private val head = fx.local(7)
    private val r = fx.local(8)

    private fun node(instr: AliasInstr, vararg succ: Int, exc: IntArray = intArrayOf()) = Node(instr, succ, exc)

    private fun cfg(vararg nodes: Node): AliasCfg = AliasCfg.direct(fx.tables, nodes.toList())

    private fun solveChecked(g: AliasCfg, initial: AliasState = AliasState.EMPTY): FixpointStates {
        val states = fp.solve(g, initial)
        assertEquals(emptyList(), checker.check(g, states, initial), "post-fixpoint check")
        return states
    }

    private fun FixpointStates.before(v: Int): AliasState = assertNotNull(statesBefore[v], "no state before $v")
    private fun FixpointStates.after(v: Int): AliasState = assertNotNull(statesAfter[v], "no state after $v")

    private fun newO(s: SiteId) = origins.allocNew(s)
    private fun oldO(s: SiteId) = origins.allocOld(s)
    private fun freshO(s: SiteId) = origins.root(bases.fresh(s))
    private fun constO(text: String) = origins.root(bases.const(STRING_TYPE, text))
    private fun const(text: String) = AliasValue.Const(bases.const(STRING_TYPE, text))
    private fun members(n: NodeId): Set<OriginId> = fx.nodes.members(n).toSet()

    @Test
    fun `loop at the first instruction joins the back edge`() {
        // Lean gLoop: 0: t = x.f; 1: x.f = v (strong), back edge 1 -> 0; 2: return t
        val px = fx.arg(0)
        val pv = fx.arg(1)
        val g = cfg(
            node(fx.load(t, px, f), 1),
            node(fx.store(px, f, pv), 0, 2),
            node(AliasInstr.Return(t)),
        )
        val st = solveChecked(g)
        val xf = fx.path(fx.argO(0), f)
        assertEquals(setOf(xf, fx.argO(1)), fx.pts(st.before(1), t))
        assertEquals(setOf(xf, fx.argO(1)), fx.cell(st.before(0), fx.argO(0), f))
        assertEquals(setOf(fx.argO(1)), fx.cell(st.after(1), fx.argO(0), f))
    }

    @Test
    fun `checker rejects the states of a simulator that ignores the back edge to the entry`() {
        val px = fx.arg(0)
        val pv = fx.arg(1)
        val withBackEdge = cfg(
            node(fx.load(t, px, f), 1),
            node(fx.store(px, f, pv), 0, 2),
            node(AliasInstr.Return(t)),
        )
        val withoutBackEdge = cfg(
            node(fx.load(t, px, f), 1),
            node(fx.store(px, f, pv), 2),
            node(AliasInstr.Return(t)),
        )
        val simulated = fp.solve(withoutBackEdge)
        assertEquals(emptyList(), checker.check(withoutBackEdge, simulated))
        val violations = checker.check(withBackEdge, simulated)
        assertTrue(violations.any { "1 -> 0" in it }, violations.toString())
    }

    @Test
    fun `checker rejects a written heap entry that holds the empty set`() {
        val g = cfg(
            node(fx.store(fx.arg(0), f, fx.arg(1)), 1),
            node(AliasInstr.Nop),
        )
        val states = solveChecked(g)
        val ed = fx.transfer.edit(states.before(1))
        ed.setHeap(heapKey(fx.argO(0), f), EMPTY_NODE)
        val broken = ed.build()
        val tampered = FixpointStates(
            arrayOf(states.statesBefore[0], broken),
            arrayOf(states.statesAfter[0], broken),
        )
        val violations = checker.check(g, tampered)
        assertTrue(violations.any { "empty" in it }, violations.toString())
    }

    @Test
    fun `handler gets the state before a throwing call`() {
        val s0 = fx.site(0)
        val s2 = fx.site(2)
        val g = cfg(
            node(fx.assign(a, AliasValue.New(s0)), 1),
            node(fx.assign(x, a), 2),
            node(AliasInstr.UnresolvedCall(s2, x.v, emptyList()), 3, exc = intArrayOf(4)),
            node(AliasInstr.Return(x)),
            node(fx.assign(e, AliasValue.Fresh(fx.site(4))), 5),
            node(AliasInstr.Return(x)),
        )
        val st = solveChecked(g)
        assertEquals(setOf(freshO(s2)), fx.pts(st.before(3), x))
        assertEquals(setOf(newO(s0), freshO(s2)), fx.pts(st.before(4), x))
        assertTrue(fx.nodes.contains(st.before(4).varNode(ETREE), OriginTable.REACHED_ALL))
    }

    @Test
    fun `kill keeps a variable that a handler reads`() {
        // live_spec_unsound: 0: x = new; 1: y = x; 2: x = m() (handler 3); 3: x.f = y; 4: nop
        val s0 = fx.site(0)
        val s2 = fx.site(2)
        val g = cfg(
            node(fx.assign(x, AliasValue.New(s0)), 1),
            node(fx.assign(y, x), 2),
            node(AliasInstr.UnresolvedCall(s2, x.v, emptyList()), 4, exc = intArrayOf(3)),
            node(fx.store(x, f, y), 4),
            node(AliasInstr.Nop),
        )
        val st = solveChecked(g)
        assertEquals(setOf(newO(s0)), fx.pts(st.before(2), x))
        assertEquals(setOf(newO(s0), freshO(s2)), fx.pts(st.before(3), x))
        assertEquals(setOf(newO(s0)), fx.pts(st.before(3), y))
        assertTrue(newO(s0) in fx.cell(st.after(3), newO(s0), f))
    }

    @Test
    fun `checker rejects the kill of a local that a handler reads`() {
        // The live set of the rule of the brief (live_spec_unsound): x is not live at the call that writes it.
        val g = cfg(
            node(fx.assign(x, AliasValue.New(fx.site(0))), 1),
            node(fx.assign(y, x), 2),
            node(AliasInstr.UnresolvedCall(fx.site(2), x.v, emptyList()), 4, exc = intArrayOf(3)),
            node(fx.store(x, f, y), 4),
            node(AliasInstr.Nop),
        )
        g.liveIn(2).clear(x.v)
        val violations = checker.check(g, fp.solve(g))
        assertTrue(violations.any { "liveness at 2" in it && "handler 3" in it }, violations.toString())
    }

    @Test
    fun `dead locals of the current context are removed and Etree Eval and other contexts stay`() {
        val other = fx.tables.vars.local(0, context = 1)
        val ed = fx.transfer.edit(AliasState.EMPTY)
        ed.setVar(other, fx.nodes.singleton(fx.argO(0)))
        ed.setVar(ETREE, fx.nodes.singleton(fx.argO(1)))
        ed.setVar(EVAL, fx.nodes.singleton(fx.argO(2)))
        val initial = ed.build()
        val g = cfg(
            node(fx.assign(x, AliasValue.New(fx.site(0))), 1),
            node(AliasInstr.Nop),
        )
        val st = solveChecked(g, initial)
        assertEquals(EMPTY_NODE, st.before(1).varNode(x.v))
        assertEquals(setOf(newO(fx.site(0))), members(st.after(0).varNode(x.v)))
        assertEquals(setOf(fx.argO(0)), members(st.before(1).varNode(other)))
        assertEquals(setOf(fx.argO(1)), members(st.before(1).varNode(ETREE)))
        assertEquals(setOf(fx.argO(2)), members(st.before(1).varNode(EVAL)))
    }

    @Test
    fun `unresolved call adds REACHED_ALL to Etree and Eval and gives a fresh result`() {
        val s0 = fx.site(0)
        val g = cfg(
            node(AliasInstr.UnresolvedCall(s0, r.v, listOf(fx.arg(0))), 1),
            node(AliasInstr.Return(r)),
        )
        val st = solveChecked(g)
        val after = st.after(0)
        assertEquals(setOf(OriginTable.REACHED_ALL), members(after.varNode(ETREE)))
        assertEquals(setOf(OriginTable.REACHED_ALL), members(after.varNode(EVAL)))
        assertEquals(setOf(freshO(s0)), fx.pts(after, r))
        assertTrue(after.heap.isEmpty())
    }

    @Test
    fun `resolved call is a provisional unresolved call`() {
        val s0 = fx.site(0)
        val g = cfg(
            node(AliasInstr.ResolvedCall(s0, r.v, emptyList()), 1),
            node(AliasInstr.Return(r)),
        )
        val st = solveChecked(g)
        assertEquals(setOf(freshO(s0)), fx.pts(st.after(0), r))
        assertEquals(setOf(OriginTable.REACHED_ALL), members(st.after(0).varNode(ETREE)))
    }

    @Test
    fun `a call blocks a later strong update`() {
        val px = fx.arg(0)
        val g = cfg(
            node(fx.store(px, f, const("a")), 1),
            node(AliasInstr.UnresolvedCall(fx.site(1), null, emptyList()), 2),
            node(fx.store(px, f, const("b")), 3),
            node(AliasInstr.Nop),
        )
        val st = solveChecked(g)
        assertEquals(setOf(constO("a")), fx.cell(st.before(1), fx.argO(0), f))
        assertEquals(setOf(constO("a"), constO("b")), fx.cell(st.before(3), fx.argO(0), f))
    }

    @Test
    fun `nested loops reach a post-fixpoint`() {
        val s0 = fx.site(0)
        val s3 = fx.site(3)
        val g = cfg(
            node(fx.assign(head, AliasValue.New(s0)), 1),
            node(AliasInstr.Nop, 2, 7),
            node(fx.assign(cur, head), 3),
            node(fx.assign(n, AliasValue.New(s3)), 4),
            node(fx.store(n, next, cur), 5),
            node(fx.assign(cur, n), 3, 6),
            node(fx.store(head, f, cur), 1),
            node(fx.load(t, head, f), 8),
            node(AliasInstr.Return(t)),
        )
        assertEquals("0 (1 2 (3 4 5) 6) 7 8", g.wto.joinToString(" ") { it.text() })
        val st = solveChecked(g)
        assertEquals(setOf(newO(s3)), fx.pts(st.before(6), cur))
        val child = members(origins.defaultNode(newO(s0), f))
        assertEquals(child + newO(s3), fx.pts(st.before(8), t))
        assertTrue(oldO(s3) in fx.cell(st.before(6), newO(s3), next))
        assertTrue(oldO(s3) in fx.cell(st.before(6), oldO(s3), next))
    }

    @Test
    fun `irreducible CFG reaches a post-fixpoint`() {
        val s1 = fx.site(1)
        val g = cfg(
            node(AliasInstr.Nop, 1, 2),
            node(fx.assign(x, AliasValue.New(s1)), 2, 3),
            node(fx.assign(y, x), 1, 3),
            node(AliasInstr.Return(y)),
        )
        val st = solveChecked(g)
        assertEquals(setOf(newO(s1), oldO(s1)), fx.pts(st.before(3), y))
    }

    @Test
    fun `unreachable node has no state`() {
        val g = cfg(
            node(AliasInstr.Return(null)),
            node(fx.assign(x, AliasValue.New(fx.site(1)))),
        )
        val st = solveChecked(g)
        assertNull(st.statesBefore[1])
        assertNull(st.statesAfter[1])
    }

    @Test
    fun `cancellation stops the fixpoint`() {
        val cancelled = DirectedFixpoint(fx.transfer, AnalysisCancellation(Duration.ZERO, null))
        val g = cfg(node(AliasInstr.Nop))
        assertFailsWith<AnalysisCancellation.AnalysisCancelled> { cancelled.solve(g) }
    }

    @Test
    fun `run checks the post-fixpoint and freezes the tables`() {
        val g = cfg(
            node(fx.assign(x, AliasValue.New(fx.site(0))), 1),
            node(AliasInstr.Return(x)),
        )
        val result = fp.run(g, verify = true)
        assertTrue(fx.nodes.isFrozen)
        assertEquals(setOf(newO(fx.site(0))), fx.pts(assertNotNull(result.statesBefore[1]), x))
        assertEquals(2, result.statesAfter.size)
    }

    private fun WtoComponent.text(): String = when (this) {
        is WtoComponent.Vertex -> "$node"
        is WtoComponent.Loop -> "($head" + body.joinToString("") { " " + it.text() } + ")"
    }
}
