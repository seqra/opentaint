package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.AliasCfg.Node
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

/**
 * Tests of the inlining of resolved calls (IMPL §5.5, §5.4; spec §5.5) on programs of the direct
 * CFG builder. A callee body has its own context. Its `this` and its arguments are the caller
 * values, as `NestedCallInstEvalCtx` gives them. Each test checks the post-fixpoint conditions of
 * the caller and of each inlined callee ([PostFixChecker]).
 */
class DirectedInlineTest {

    private val fx = DirectedEngineFixture()
    private val fp = DirectedFixpoint(fx.transfer)
    private val checker = PostFixChecker(fp)
    private val origins = fx.origins
    private val bases = fx.bases
    private val tables = fx.tables
    private val f = fx.field("f")
    private val g = fx.field("g")

    // Caller locals (root context).
    private val x = fx.local(0)
    private val a = fx.local(1)
    private val h = fx.local(2)
    private val t = fx.local(3)
    private val r = fx.local(4)
    private val last = fx.local(5)
    private val b = fx.local(6)

    private fun calleeLocal(i: Int, context: Int) = AliasValue.Local(tables.vars.local(i, context))
    private fun calleeSite(i: Int, context: Int): SiteId = tables.sites.site(i, context)

    private fun node(instr: AliasInstr, vararg succ: Int, exc: IntArray = intArrayOf()) = Node(instr, succ, exc)

    /** A callee body. [builds] counts the CFG builds of this body. */
    private inner class Callee(val context: Int, val nodes: List<Node>, val entry: Int = 0) {
        var builds = 0
        var lastCallOnCycle: Boolean? = null

        fun build(callOnCycle: Boolean): AliasCfg {
            builds++
            lastCallOnCycle = callOnCycle
            return AliasCfg.direct(tables, nodes, entry, context, callOnCycle)
        }
    }

    private fun bodies(vararg callees: Callee) = CalleeBodies { onCycle -> callees.map { it.build(onCycle) } }

    private fun call(
        site: SiteId,
        result: AliasValue.Local?,
        args: List<AliasValue>,
        vararg callees: Callee,
        models: List<PassThrough> = emptyList(),
    ) = AliasInstr.ResolvedCall(site, result?.v, args, models, bodies(*callees))

    private fun cfg(vararg nodes: Node): AliasCfg = AliasCfg.direct(tables, nodes.toList())

    private fun solveChecked(cfg: AliasCfg): FixpointStates {
        val states = fp.solve(cfg)
        assertEquals(emptyList(), checker.check(cfg, states), "post-fixpoint check")
        return states
    }

    private fun FixpointStates.before(v: Int): AliasState = assertNotNull(statesBefore[v], "no state before $v")
    private fun FixpointStates.after(v: Int): AliasState = assertNotNull(statesAfter[v], "no state after $v")

    private fun members(n: NodeId): Set<OriginId> = fx.nodes.members(n).toSet()
    private fun freshO(s: SiteId) = origins.root(bases.fresh(s))
    private fun constO(text: String) = origins.root(bases.const(STRING_TYPE, text))
    private fun const(text: String) = AliasValue.Const(bases.const(STRING_TYPE, text))

    /** The contexts of the locals of [st]. */
    private fun contexts(st: AliasState): Set<Int> {
        val out = HashSet<Int>()
        st.forEachVar { v, _ -> tables.vars.key(v)?.let { out += it.context } }
        return out
    }

    /**
     * Lean `inlined_answer` (`Impl/CfgExamples.lean`): the callee `this' = x; this'.f = a; ex = new;
     * throw ex` is spliced into the caller. Each callee node has an exceptional edge to the caller
     * handler. The handler reads `x.f`. The real alias `t ~ a` is found.
     */
    private fun calleeWritesThenThrows(context: Int) = Callee(
        context,
        listOf(
            node(fx.store(x, f, a), 1),
            node(AliasInstr.Assign(calleeLocal(0, context).v, AliasValue.New(calleeSite(1, context))), 2),
            node(AliasInstr.Throw(calleeLocal(0, context))),
        ),
    )

    private fun handlerProgram(call: AliasInstr): AliasCfg = cfg(
        node(fx.assign(x, AliasValue.New(fx.site(0))), 1),
        node(fx.assign(a, fx.arg(0)), 2),
        node(call, 3, exc = intArrayOf(4)),
        node(AliasInstr.Nop, 5),
        node(fx.assign(h, AliasValue.Fresh(fx.site(4))), 5),
        node(fx.load(t, x, f), 6),
        node(AliasInstr.Return(t)),
    )

    @Test
    fun `callee writes this f then throws and the handler sees x f alias a`() {
        val callee = calleeWritesThenThrows(context = 1)
        val program = handlerProgram(call(fx.site(2), null, listOf(x, a), callee))
        val st = solveChecked(program)

        // The callee writes x.f = a with a strong update (new(s0) is unique, Etree is empty).
        assertTrue(fx.argO(0) in fx.pts(st.before(6), t), "t ~ a after the handler")
        assertTrue(fx.argO(0) in fx.cell(st.before(4), origins.allocNew(fx.site(0)), f))
        // The callee variables are removed from the handler state.
        assertEquals(setOf(ROOT_CONTEXT), contexts(st.before(4)))
        // The callee always throws: no return state, so the normal exit is the unresolved call rule.
        assertTrue(fx.argO(0) !in fx.cell(st.after(2), origins.allocNew(fx.site(0)), f))
    }

    @Test
    fun `checker rejects a handler state without the states of the callee nodes`() {
        val callee = calleeWritesThenThrows(context = 1)
        val program = handlerProgram(call(fx.site(2), null, listOf(x, a), callee))
        val st = solveChecked(program)

        // The handler state of a rule without the callee nodes: the states before and after the call.
        val joined = fx.transfer.join(st.before(2), st.after(2)).state
        val broken = fp.kill(program, 4, joined)
        val before = st.statesBefore.copyOf()
        before[4] = broken
        val violations = checker.check(program, FixpointStates(before, st.statesAfter))
        assertTrue(violations.any { "callee" in it && "-> 4" in it }, violations.toString())
    }

    @Test
    fun `handler sees the write of a nested inlined callee`() {
        // Depth 2: the caller calls A (context 1), A calls B (context 2), B writes x.f = a and throws.
        val inner = calleeWritesThenThrows(context = 2)
        val outer = Callee(
            1,
            listOf(
                node(call(calleeSite(0, 1), null, listOf(x, a), inner), 1),
                node(AliasInstr.Return(null)),
            ),
        )
        val program = handlerProgram(call(fx.site(2), null, listOf(x, a), outer))
        val st = solveChecked(program)
        assertTrue(fx.argO(0) in fx.pts(st.before(6), t), "t ~ a after the handler")
        assertEquals(setOf(ROOT_CONTEXT), contexts(st.before(4)))
    }

    @Test
    fun `getter result gets the returned value and the callee locals are removed`() {
        // Callee getter: v = this.f; return v. The caller `this` is the callee `this`.
        val v = calleeLocal(0, 1)
        val getter = Callee(
            1,
            listOf(
                node(AliasInstr.FieldLoad(v.v, AliasValue.This, f), 1),
                node(AliasInstr.Return(v)),
            ),
        )
        val program = cfg(
            node(call(fx.site(0), r, listOf(AliasValue.This), getter), 1),
            node(AliasInstr.Return(r)),
        )
        val st = solveChecked(program)
        assertEquals(setOf(fx.path(fx.thisO(), f)), fx.pts(st.after(0), r))
        assertEquals(setOf(ROOT_CONTEXT), contexts(st.after(0)))
        // No closure: the inlined call adds nothing to Etree and Eval.
        assertEquals(EMPTY_NODE, st.after(0).varNode(ETREE))
    }

    @Test
    fun `setter then getter gives the stored argument`() {
        val setter = Callee(
            1,
            listOf(
                node(fx.store(AliasValue.This, f, fx.arg(0)), 1),
                node(AliasInstr.Return(null)),
            ),
        )
        val v = calleeLocal(0, 2)
        val getter = Callee(
            2,
            listOf(
                node(AliasInstr.FieldLoad(v.v, AliasValue.This, f), 1),
                node(AliasInstr.Return(v)),
            ),
        )
        val program = cfg(
            node(call(fx.site(0), null, listOf(AliasValue.This, fx.arg(0)), setter), 1),
            node(call(fx.site(1), r, listOf(AliasValue.This), getter), 2),
            node(AliasInstr.Return(r)),
        )
        val st = solveChecked(program)
        assertEquals(setOf(fx.argO(0)), fx.pts(st.after(1), r))
    }

    @Test
    fun `the call result is the join over the returns of all overrides`() {
        // Override 1 has two returns (arg0 and arg1). Override 2 returns a constant.
        val o1 = Callee(
            1,
            listOf(
                node(AliasInstr.Nop, 1, 2),
                node(AliasInstr.Return(fx.arg(0))),
                node(AliasInstr.Return(fx.arg(1))),
            ),
        )
        val o2 = Callee(2, listOf(node(AliasInstr.Return(const("s")))))
        val program = cfg(
            node(call(fx.site(0), r, listOf(fx.arg(0), fx.arg(1)), o1, o2), 1),
            node(AliasInstr.Return(r)),
        )
        val st = solveChecked(program)
        assertEquals(setOf(fx.argO(0), fx.argO(1), constO("s")), fx.pts(st.after(0), r))
    }

    @Test
    fun `a return of null in the callee gets the callee site`() {
        val s = calleeSite(0, 1)
        val callee = Callee(1, listOf(node(AliasInstr.Return(AliasValue.Null(s)))))
        val program = cfg(
            node(call(fx.site(0), r, emptyList(), callee), 1),
            node(AliasInstr.Return(r)),
        )
        val st = solveChecked(program)
        assertEquals(setOf(origins.root(bases.nullAt(s))), fx.pts(st.after(0), r))
    }

    @Test
    fun `a call without a return state is an unresolved call with the models`() {
        val callee = calleeWritesThenThrows(context = 1)
        val s0 = fx.site(0)
        val model = PassThrough(ModelPath(ModelBase.Value(fx.arg(0))), ModelPath(ModelBase.Result))
        val program = cfg(
            node(call(s0, r, listOf(fx.arg(0)), callee, models = listOf(model)), 1),
            node(AliasInstr.Return(r)),
        )
        val st = solveChecked(program)
        assertEquals(setOf(freshO(s0), fx.argO(0)), fx.pts(st.after(0), r))
        assertEquals(setOf(fx.argO(0), OriginTable.REACHED_STATICS), members(st.after(0).varNode(ETREE)))
    }

    @Test
    fun `a resolved call without a callee body is an unresolved call with the models`() {
        val s0 = fx.site(0)
        val model = PassThrough(ModelPath(ModelBase.Value(fx.arg(0))), ModelPath(ModelBase.Result))
        val program = cfg(
            node(AliasInstr.ResolvedCall(s0, r.v, listOf(fx.arg(0)), listOf(model)), 1),
            node(AliasInstr.Return(r)),
        )
        val st = solveChecked(program)
        assertEquals(setOf(freshO(s0), fx.argO(0)), fx.pts(st.after(0), r))
        assertEquals(setOf(fx.argO(0), OriginTable.REACHED_STATICS), members(st.after(0).varNode(ETREE)))
    }

    /**
     * Caller: `e = x.f; m(x); t = x.f; t.g = v; w = e.g`. The call `m` has the override `A` with an
     * empty body. If [bodiless] is true, it also has an override without a body (a native method).
     */
    private fun bodilessOverrideProgram(bodiless: Boolean, exc: IntArray = intArrayOf()): AliasCfg {
        val px = fx.arg(0)
        val empty = Callee(1, listOf(node(AliasInstr.Return(null))))
        val bodies = bodies(empty)
        val withMissing = if (!bodiless) bodies else object : CalleeBodies {
            override fun build(callOnCycle: Boolean): List<AliasCfg> = bodies.build(callOnCycle)
            override val hasBodilessOverride: Boolean get() = true
        }
        val e = a
        val w = b
        return cfg(
            node(fx.load(e, px, f), 1),
            node(AliasInstr.ResolvedCall(fx.site(1), null, listOf(px), callees = withMissing), 2, exc = exc),
            node(fx.load(t, px, f), 3),
            node(fx.store(t, g, fx.arg(1)), 4),
            node(fx.load(w, e, g), 5),
            node(AliasInstr.Return(w)),
            node(fx.assign(h, AliasValue.Fresh(fx.site(6))), 7),
            node(AliasInstr.Return(h)),
        )
    }

    @Test
    fun `an override without a body also applies the unresolved call rule`() {
        val xfg = fx.path(fx.argO(0), f, g)

        // Control: only the empty body. The store t.g = v is strong, so e.g holds v only.
        val strong = solveChecked(bodilessOverrideProgram(bodiless = false))
        assertEquals(setOf(fx.argO(1)), fx.pts(strong.after(4), b))

        // An override without a body can write x.f: the call closure reaches x, so the store is weak.
        val st = solveChecked(bodilessOverrideProgram(bodiless = true))
        assertTrue(fx.argO(0) in members(st.after(1).varNode(ETREE)), "the call closure reaches x")
        assertEquals(setOf(fx.argO(1), xfg), fx.pts(st.after(4), b))
    }

    @Test
    fun `an override without a body joins the call closure into the exceptional exit`() {
        val program = bodilessOverrideProgram(bodiless = true, exc = intArrayOf(6))
        val st = solveChecked(program)
        assertTrue(fx.argO(0) in members(st.before(6).varNode(ETREE)), "the handler sees the call closure")

        // The checker asks for the partial call of the override without a body at the handler.
        val before = st.statesBefore.copyOf()
        before[6] = fp.kill(program, 6, st.before(1))
        val violations = checker.check(program, FixpointStates(before, st.statesAfter, st.exits))
        assertTrue(violations.any { "-> 6 (call)" in it }, violations.toString())
    }

    @Test
    fun `an unresolved call in the callee grows Etree of the caller`() {
        // Caller: t = x.f; t.g = "a"; A(x); t.g = "b". A: m(this) (unresolved). The last store is weak.
        val px = fx.arg(0)
        val callee = Callee(
            1,
            listOf(
                node(AliasInstr.UnresolvedCall(calleeSite(0, 1), null, listOf(px)), 1),
                node(AliasInstr.Return(null)),
            ),
        )
        val program = cfg(
            node(fx.load(t, px, f), 1),
            node(fx.store(t, g, const("a")), 2),
            node(call(fx.site(2), null, listOf(px), callee), 3),
            node(fx.store(t, g, const("b")), 4),
            node(AliasInstr.Return(t)),
        )
        val st = solveChecked(program)
        val xf = fx.path(fx.argO(0), f)
        // Etree has the argument, the marker, and the symbolic content of the reached written cell.
        assertEquals(
            setOf(fx.argO(0), OriginTable.REACHED_STATICS, constO("a")),
            members(st.after(2).varNode(ETREE)),
        )
        assertEquals(setOf(constO("a"), constO("b")), fx.cell(st.after(3), xf, g))
    }

    @Test
    fun `a callee CFG is built once and its sites are loop sites if the call is on a caller cycle`() {
        // Caller: 0: last = null; loop: 1: b = make(); 2: b.f = last; 3: last = b; back to 1.
        // make: n = new; return n.
        val n = calleeLocal(0, 1)
        val s = calleeSite(0, 1)
        val make = Callee(
            1,
            listOf(
                node(AliasInstr.Assign(n.v, AliasValue.New(s)), 1),
                node(AliasInstr.Return(n)),
            ),
        )
        val program = cfg(
            node(fx.assign(last, AliasValue.Null(fx.site(0))), 1),
            node(call(fx.site(1), b, emptyList(), make), 2),
            node(fx.store(b, f, last), 3),
            node(fx.assign(last, b), 1, 4),
            node(AliasInstr.Return(last)),
        )
        assertFalse(tables.sites.isLoopSite(s))
        val st = solveChecked(program)
        assertEquals(1, make.builds, "one CFG build for each call statement and override")
        assertEquals(true, make.lastCallOnCycle)
        assertTrue(tables.sites.isLoopSite(s))
        // The new object of the callee site retires in the caller loop: the object of the last
        // iteration holds the older objects of the site and the null of the first iteration.
        val nw = origins.allocNew(s)
        val old = origins.allocOld(s)
        assertEquals(setOf(nw), fx.pts(st.before(4), last))
        assertEquals(setOf(old, origins.root(bases.nullAt(fx.site(0)))), fx.cell(st.before(4), nw, f))
    }

    @Test
    fun `a nested callee site is a loop site if the outer call is on a caller cycle`() {
        val n = calleeLocal(0, 2)
        val s = calleeSite(0, 2)
        val inner = Callee(
            2,
            listOf(
                node(AliasInstr.Assign(n.v, AliasValue.New(s)), 1),
                node(AliasInstr.Return(n)),
            ),
        )
        val m = calleeLocal(0, 1)
        val outer = Callee(
            1,
            listOf(
                node(call(calleeSite(0, 1), m, emptyList(), inner), 1),
                node(AliasInstr.Return(m)),
            ),
        )
        val program = cfg(
            node(fx.assign(last, AliasValue.Null(fx.site(0))), 1),
            node(call(fx.site(1), b, emptyList(), outer), 2),
            node(fx.store(b, f, last), 3),
            node(fx.assign(last, b), 1, 4),
            node(AliasInstr.Return(last)),
        )
        solveChecked(program)
        assertEquals(1, outer.builds)
        assertEquals(1, inner.builds)
        assertEquals(true, inner.lastCallOnCycle)
        assertTrue(tables.sites.isLoopSite(s))
    }

    @Test
    fun `two call statements of one body have their own callee sites`() {
        val make1 = Callee(1, listOf(node(AliasInstr.Return(AliasValue.Fresh(calleeSite(0, 1))))))
        val make2 = Callee(2, listOf(node(AliasInstr.Return(AliasValue.Fresh(calleeSite(0, 2))))))
        val program = cfg(
            node(call(fx.site(0), a, emptyList(), make1), 1),
            node(call(fx.site(1), b, emptyList(), make2), 2),
            useNode(AliasInstr.Nop, extraUses(a, b)),
        )
        val st = fp.solve(program)
        assertEquals(emptyList(), checker.check(program, st))
        assertEquals(setOf(freshO(calleeSite(0, 1))), fx.pts(st.after(1), a))
        assertEquals(setOf(freshO(calleeSite(0, 2))), fx.pts(st.after(1), b))
        assertTrue(calleeSite(0, 1) != calleeSite(0, 2))
        // A fresh origin of a callee site that is not a loop site is unique.
        assertTrue(origins.uniqueByKind(freshO(calleeSite(0, 1))))
    }

    private fun useNode(instr: AliasInstr, extraUses: IntArray) = Node(instr, extraUses = extraUses)

    private fun extraUses(vararg v: AliasValue.Local) = v.map { it.v }.toIntArray()

    @Test
    fun `marking a loop site two times is allowed after its new object exists`() {
        val s = fx.site(100)
        tables.sites.markLoopSite(s)
        origins.allocNew(s)
        tables.sites.markLoopSite(s)
        assertTrue(tables.sites.isLoopSite(s))
    }
}
