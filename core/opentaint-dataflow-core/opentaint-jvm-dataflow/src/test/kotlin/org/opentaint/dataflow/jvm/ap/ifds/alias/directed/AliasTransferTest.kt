package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertNotEquals
import kotlin.test.assertSame
import kotlin.test.assertTrue

class AliasTransferTest {

    private val fx = DirectedEngineFixture()
    private val tr = fx.transfer
    private val origins = fx.origins
    private val bases = fx.bases
    private val f = fx.field("f")
    private val g = fx.field("g")
    private val next = fx.field("next")

    private val x = fx.arg(0)
    private val y = fx.arg(1)
    private val z = fx.arg(2)
    private val w = fx.arg(3)
    private val a = fx.local(0)
    private val b = fx.local(1)
    private val t = fx.local(2)
    private val u = fx.local(3)
    private val n = fx.local(4)
    private val p = fx.local(5)
    private val q = fx.local(6)
    private val r = fx.local(7)

    private val xo = fx.argO(0)
    private val yo = fx.argO(1)
    private val zo = fx.argO(2)
    private val wo = fx.argO(3)

    /** `if (c) a = x; else a = y;` */
    private fun aIsXorY(): AliasState = tr.join(fx.run(fx.assign(a, x)), fx.run(fx.assign(a, y))).state

    // ---- Assignments (IMPL §4.1) ----

    @Test
    fun `copy shares the node`() {
        val st = fx.run(fx.assign(a, x), fx.assign(b, a))
        assertEquals(st.varNode(a.v), st.varNode(b.v))
        assertEquals(fx.set(xo), fx.pts(st, b))
    }

    @Test
    fun `null sites are distinct for each statement and a copy of a null aliases it`() {
        // spec 6.6: p = null; q = null; r = p
        val s0 = fx.site(10)
        val s1 = fx.site(11)
        val st = fx.run(
            fx.assign(p, AliasValue.Null(s0)),
            fx.assign(q, AliasValue.Null(s1)),
            fx.assign(r, p),
        )
        val p0 = origins.root(bases.nullAt(s0))
        val q1 = origins.root(bases.nullAt(s1))
        assertEquals(fx.set(p0), fx.pts(st, p))
        assertEquals(fx.set(q1), fx.pts(st, q))
        assertNotEquals(p0, q1)
        assertEquals(fx.pts(st, p), fx.pts(st, r))
        assertEquals(BaseKind.NULL, bases.kind(origins.base(p0)))
    }

    @Test
    fun `a stored null gets the site of the store`() {
        // n = new N() at 5; n.g = null at 6: H(new(5), g) = {null(6)} (strong)
        val s5 = fx.site(5)
        val s6 = fx.site(6)
        val st = fx.run(
            fx.assign(n, AliasValue.New(s5)),
            fx.store(n, g, AliasValue.Null(s6)),
            fx.load(a, n, f),
            fx.load(b, n, g),
        )
        assertEquals(fx.set(origins.root(bases.nullAt(s6))), fx.cell(st, origins.allocNew(s5), g))
        assertEquals(fx.set(origins.root(bases.allocChild(s5, f))), fx.pts(st, a))
        assertEquals(fx.set(origins.root(bases.nullAt(s6))), fx.pts(st, b))
    }

    @Test
    fun `constants are shared by value and never unique`() {
        val abc = bases.const(STRING_TYPE, "abc")
        val st = fx.run(
            fx.assign(a, AliasValue.Const(abc)),
            fx.assign(b, AliasValue.Const(bases.const(STRING_TYPE, "abc"))),
            fx.assign(t, AliasValue.Const(bases.const(STRING_TYPE, "other"))),
        )
        assertEquals(st.varNode(a.v), st.varNode(b.v))
        assertNotEquals(st.varNode(a.v), st.varNode(t.v))
        val c = origins.root(abc)
        assertFalse(tr.isUnique(st, c))

        // Two stores into the constant keep both values (weak).
        val st2 = fx.run(fx.store(a, f, x), fx.store(b, f, y), from = st)
        assertEquals(fx.set(origins.child(c, f), xo, yo), fx.cell(st2, c, f))
    }

    @Test
    fun `class constants are keyed by the class`() {
        val st = fx.run(
            fx.assign(a, AliasValue.Const(bases.const(CLASS_TYPE, "a.B"))),
            fx.assign(b, AliasValue.Const(bases.const(CLASS_TYPE, "a.B"))),
            fx.assign(t, AliasValue.Const(bases.const(STRING_TYPE, "a.B"))),
        )
        assertEquals(st.varNode(a.v), st.varNode(b.v))
        assertNotEquals(st.varNode(a.v), st.varNode(t.v))
    }

    @Test
    fun `a box of a constant is shared and a box of another value is one origin for each site`() {
        val s1 = fx.site(1)
        val s2 = fx.site(2)
        val st = fx.run(
            fx.assign(a, AliasValue.Const(bases.const("java.lang.Integer", "1"))),
            fx.assign(b, AliasValue.Const(bases.const("java.lang.Integer", "1"))),
            fx.assign(t, AliasValue.Box(s1)),
            fx.assign(u, AliasValue.Box(s2)),
        )
        assertEquals(st.varNode(a.v), st.varNode(b.v))
        assertNotEquals(st.varNode(t.v), st.varNode(u.v))
        assertEquals(fx.set(origins.root(bases.box(s1))), fx.pts(st, t))
        for (v in listOf(a, t, u)) {
            val o = fx.pts(st, v).single()
            assertFalse(tr.isUnique(st, o), "box origin must not be unique")
        }
        // A store into a box is weak.
        val st2 = fx.run(fx.store(t, f, x), fx.store(t, f, y), from = st)
        val bo = origins.root(bases.box(s1))
        assertEquals(fx.set(origins.child(bo, f), xo, yo), fx.cell(st2, bo, f))
    }

    @Test
    fun `fresh values have the root of their site`() {
        val s = fx.site(3)
        val st = fx.run(fx.assign(a, AliasValue.Fresh(s)))
        assertEquals(fx.set(origins.root(bases.fresh(s))), fx.pts(st, a))
        assertTrue(tr.isUnique(st, origins.root(bases.fresh(s))))
        val loop = fx.loopSite(4)
        assertFalse(tr.isUnique(st, origins.root(bases.fresh(loop))))
    }

    // ---- Statics ----

    @Test
    fun `static read is keyed by the class and a static write changes nothing`() {
        // spec 6.8: C.f = v; t = C.f; u = C.f; t.g = z
        val st0 = fx.run(fx.assign(a, x))
        val st1 = tr.transfer(st0, AliasInstr.StaticWrite)
        assertSame(st0, st1)
        val st = fx.run(fx.staticRead(t, "a.C", f), fx.staticRead(u, "a.C", f), fx.store(t, g, z), from = st1)
        val cf = origins.child(origins.root(bases.static("a.C")), f)
        assertEquals(fx.set(cf), fx.pts(st, t))
        assertEquals(st.varNode(t.v), st.varNode(u.v))
        // Strong update: <C.f> is unique and no call came before.
        assertEquals(fx.set(zo), fx.cell(st, cf, g))
        // Another class gives another origin.
        val st2 = fx.run(fx.staticRead(b, "a.D", f), from = st)
        assertNotEquals(st2.varNode(t.v), st2.varNode(b.v))
    }

    // ---- Load ----

    @Test
    fun `load of an unwritten cell gives its default content`() {
        // spec 6.4: if (c) a = x; else a = y; t = a.f
        val st = fx.run(fx.load(t, a, f), from = aIsXorY())
        assertEquals(fx.set(fx.path(xo, f), fx.path(yo, f)), fx.pts(st, t))
        assertEquals(0, st.heap.size)
    }

    @Test
    fun `array load and store use the element cell`() {
        val st = fx.run(fx.astore(x, y), fx.aload(t, x))
        assertEquals(fx.set(fx.path(xo, ELEM_CELL), yo), fx.pts(st, t))
    }

    // ---- Store (IMPL §4.2) ----

    @Test
    fun `strong update on a unique origin`() {
        // spec 6.3: b = x.f; x.f = z; t = x.f
        val st = fx.run(fx.load(b, x, f), fx.store(x, f, z), fx.load(t, x, f))
        assertEquals(fx.set(zo), fx.pts(st, t))
        assertEquals(fx.set(fx.path(xo, f)), fx.pts(st, b))
        assertEquals(fx.set(zo), fx.cell(st, xo, f))
    }

    @Test
    fun `weak update on two origins`() {
        // spec 6.2: if (c) a = x; else a = y; a.f = z; a = w
        val st = fx.run(fx.store(a, f, z), fx.assign(a, w), from = aIsXorY())
        assertEquals(fx.set(fx.path(xo, f), zo), fx.cell(st, xo, f))
        assertEquals(fx.set(fx.path(yo, f), zo), fx.cell(st, yo, f))
        assertEquals(fx.set(wo), fx.pts(st, a))
    }

    @Test
    fun `array store is always weak`() {
        val st = fx.run(fx.astore(x, y), fx.astore(x, z))
        assertEquals(fx.set(fx.path(xo, ELEM_CELL), yo, zo), fx.cell(st, xo, ELEM_CELL))
    }

    @Test
    fun `store shortcut makes a strong update without the uniqueness test`() {
        // old(s) is never unique. H(old(s), f) = {@s.f} is a subset of the value, so strong == weak.
        val s = fx.loopSite(5)
        val old = origins.allocOld(s)
        val child = origins.root(bases.allocChild(s, f))
        val st0 = AliasState.EMPTY
        val base = fx.node(old)
        val v = fx.node(child, zo)
        assertFalse(tr.isUnique(st0, old))
        val viaStore = tr.store(st0, base, f, v)
        assertEquals(fx.set(child, zo), fx.cell(viaStore, old, f))
        assertEquals(tr.storeWeak(st0, base, f, v), viaStore)
        assertEquals(tr.put(st0, old, f, v), viaStore)
    }

    @Test
    fun `first write of a value that the cell already holds needs no test`() {
        // t = x.f; x.f = t with <x> in Etree: the shortcut keeps the state.
        val st0 = fx.withSets(fx.run(fx.load(t, x, f)), fx.node(xo), EMPTY_NODE)
        val st = fx.run(fx.store(x, f, t), from = st0)
        assertEquals(st0, st)
    }

    @Test
    fun `a reached proper prefix makes the store weak`() {
        // spec 6.7: <x.f> has the reached prefix <x>.
        val xf = fx.path(xo, f)
        val st0 = fx.withSets(fx.run(fx.load(u, x, f)), fx.node(xo), EMPTY_NODE)
        assertFalse(tr.isUnique(st0, xf))
        val st = fx.run(fx.store(u, g, z), from = st0)
        assertEquals(fx.set(fx.path(xf, g), zo), fx.cell(st, xf, g))
        // The origin itself in Etree is not a proper prefix: <x> stays unique.
        assertTrue(tr.isUnique(st0, xo))
    }

    @Test
    fun `an origin in Eval is not unique`() {
        val s = fx.site(5)
        val nw = origins.allocNew(s)
        val st0 = fx.withSets(fx.run(fx.assign(t, AliasValue.New(s))), EMPTY_NODE, fx.node(nw))
        assertFalse(tr.isUnique(st0, nw))
        val st = fx.run(fx.store(t, g, x), from = st0)
        assertEquals(fx.set(origins.root(bases.allocChild(s, g)), xo), fx.cell(st, nw, g))
    }

    @Test
    fun `marker reached all blocks every strong update`() {
        val st0 = fx.withSets(AliasState.EMPTY, fx.node(OriginTable.REACHED_ALL), fx.node(OriginTable.REACHED_ALL))
        assertFalse(tr.isUnique(st0, xo))
        assertFalse(tr.isUnique(st0, origins.allocNew(fx.site(1))))
        val st = fx.run(fx.store(x, f, z), from = st0)
        assertEquals(fx.set(fx.path(xo, f), zo), fx.cell(st, xo, f))
    }

    @Test
    fun `marker reached statics blocks strong updates below a static root`() {
        // spec 6.8: t = C.f; m(); u.g = w is weak.
        val st0 = fx.withSets(AliasState.EMPTY, fx.node(OriginTable.REACHED_STATICS), EMPTY_NODE)
        val cf = fx.path(origins.root(bases.static("a.C")), f)
        assertFalse(tr.isUnique(st0, cf))
        assertTrue(tr.isUnique(st0, xo))
        val st = fx.run(fx.staticRead(u, "a.C", f), fx.store(u, g, w), from = st0)
        assertEquals(fx.set(fx.path(cf, g), wo), fx.cell(st, cf, g))
    }

    @Test
    fun `allocation of a loop site is unique as new and not as old`() {
        // spec 6.3: while (c) { n = new Node(); n.f = x; n.f = y; }
        val s = fx.loopSite(7)
        val nw = origins.allocNew(s)
        val old = origins.allocOld(s)
        val body = arrayOf(fx.assign(n, AliasValue.New(s)), fx.store(n, f, x), fx.store(n, f, y))
        val it1 = fx.run(*body)
        assertEquals(fx.set(nw), fx.pts(it1, n))
        assertEquals(fx.set(yo), fx.cell(it1, nw, f))
        val it2 = fx.run(*body, from = it1)
        assertEquals(fx.set(yo), fx.cell(it2, nw, f))
        // The objects of earlier iterations keep <y>.
        assertEquals(fx.set(origins.root(bases.allocChild(s, f)), yo), fx.cell(it2, old, f))
        assertFalse(tr.isUnique(it2, old))
    }

    // ---- Retire (IMPL §4.3) ----

    @Test
    fun `retire merges a written cell of old with the default of new (retireNaive_ne)`() {
        val s = fx.loopSite(0)
        val old = origins.allocOld(s)
        val st0 = tr.put(AliasState.EMPTY, old, f, fx.node(old))
        val st = tr.retire(st0, s)
        assertEquals(fx.set(origins.root(bases.allocChild(s, f)), old), fx.cell(st, old, f))
    }

    @Test
    fun `retire renames new to old in every env and heap node and in both sets`() {
        val s = fx.loopSite(1)
        val nw = origins.allocNew(s)
        val old = origins.allocOld(s)
        // n = new; n.next = n; x.f = n; a = n; Etree = Eval = {new}
        val st0 = fx.withSets(
            fx.run(
                fx.assign(n, AliasValue.New(s)),
                fx.store(n, next, n),
                fx.store(x, f, n),
                fx.assign(a, n),
            ),
            fx.node(nw), fx.node(nw, xo),
        )
        val st = tr.retire(st0, s)
        assertEquals(fx.set(old), fx.pts(st, a))
        assertEquals(fx.set(old), fx.pts(st, n))
        assertEquals(fx.set(old), fx.cell(st, xo, f))
        assertEquals(fx.set(old), fx.nodes.members(st.varNode(ETREE)).toSet())
        assertEquals(fx.set(old, xo), fx.nodes.members(st.varNode(EVAL)).toSet())
        // The cell of new moves to old, with the default of the retired object.
        assertEquals(fx.set(origins.root(bases.allocChild(s, next)), old), fx.cell(st, old, next))
        // new(s) gets its default content.
        assertFalse(st.isWritten(heapKey(nw, next)))
        assertEquals(fx.set(origins.root(bases.allocChild(s, next))), fx.cell(st, nw, next))
        // No node holds new(s) after the retire.
        st.forEachVar { _, node -> assertFalse(fx.nodes.contains(node, nw)) }
        st.forEachHeap { _, node -> assertFalse(fx.nodes.contains(node, nw)) }
    }

    @Test
    fun `retire of a state without the site changes nothing`() {
        val s = fx.loopSite(2)
        val st0 = fx.run(fx.store(x, f, z))
        assertEquals(st0, tr.retire(st0, s))
    }

    @Test
    fun `only a loop site retires`() {
        val s = fx.site(3)
        val nw = origins.allocNew(s)
        // A non-loop site does not retire. The test forces a state that holds new(s) before the statement.
        val st0 = fx.run(fx.assign(a, AliasValue.New(s)), fx.store(a, f, x))
        val st = fx.run(fx.assign(b, AliasValue.New(s)), from = st0)
        assertEquals(fx.set(nw), fx.pts(st, a))
        assertEquals(fx.set(xo), fx.cell(st, nw, f))
    }

    @Test
    fun `a stored new value retires before the base is read`() {
        // n = new at 4 (loop); n.next = new at 4: n now holds old(4), the new object is new(4).
        val s = fx.loopSite(4)
        val st = fx.run(fx.assign(n, AliasValue.New(s)), fx.store(n, next, AliasValue.New(s)))
        val old = origins.allocOld(s)
        val nw = origins.allocNew(s)
        assertEquals(fx.set(old), fx.pts(st, n))
        // old(s) is not unique: weak store into old(s).next.
        assertEquals(fx.set(origins.root(bases.allocChild(s, next)), nw), fx.cell(st, old, next))
    }

    // ---- Join (IMPL §4.6) ----

    @Test
    fun `join with absent keys uses the default content and the empty set`() {
        val s1 = fx.run(fx.store(x, f, z), fx.assign(a, x))
        val s2 = fx.run(fx.assign(b, y))
        val j = tr.join(s1, s2)
        assertTrue(j.changed)
        assertEquals(fx.set(fx.path(xo, f), zo), fx.cell(j.state, xo, f))
        assertEquals(fx.set(xo), fx.pts(j.state, a))
        assertEquals(fx.set(yo), fx.pts(j.state, b))
        assertEquals(tr.join(s2, s1).state, j.state)
    }

    @Test
    fun `join of a written cell and an unwritten cell adds the default content`() {
        val s1 = fx.run(fx.load(t, x, f), fx.store(x, f, z))
        val s2 = fx.run(fx.load(t, x, f))
        val j = tr.join(s1, s2)
        assertEquals(fx.set(fx.path(xo, f), zo), fx.cell(j.state, xo, f))
        val j2 = tr.join(s2, s2)
        assertFalse(j2.changed)
        assertSame(s2, j2.state)
    }

    @Test
    fun `join flag is false when the second state is included`() {
        val big = aIsXorY()
        val small = fx.run(fx.assign(a, x))
        val j = tr.join(big, small)
        assertFalse(j.changed)
        assertEquals(big, j.state)
        val j2 = tr.join(small, big)
        assertTrue(j2.changed)
        assertEquals(big, j2.state)
    }

    @Test
    fun `join includes the reserved keys`() {
        val s1 = fx.withSets(AliasState.EMPTY, fx.node(xo), EMPTY_NODE)
        val s2 = fx.withSets(AliasState.EMPTY, fx.node(yo), fx.node(zo))
        val j = tr.join(s1, s2)
        assertEquals(fx.set(xo, yo), fx.nodes.members(j.state.varNode(ETREE)).toSet())
        assertEquals(fx.set(zo), fx.nodes.members(j.state.varNode(EVAL)).toSet())
    }

    @Test
    fun `loop over a list stops at deep with K = 2`() {
        // spec 6.5: x = h; while (c) { x = x.next; }
        val k2 = DirectedEngineFixture(symDepth = 2)
        val nx = k2.field("next")
        val h = k2.arg(0)
        val xv = k2.local(0)
        val ho = k2.argO(0)
        val entry = k2.run(k2.assign(xv, h))
        var head = entry
        var iterations = 0
        while (true) {
            iterations++
            val after = k2.run(k2.load(xv, xv, nx), from = head)
            val j = k2.transfer.join(head, after)
            if (!j.changed) break
            head = j.state
            check(iterations < 10)
        }
        val deep = k2.origins.deep(k2.bases.arg(0))
        assertEquals(
            k2.set(ho, k2.path(ho, nx), k2.path(ho, nx, nx), deep),
            k2.pts(head, xv),
        )
        assertEquals(4, iterations)
    }

    // ---- Calls (DirectedFixpoint.evaluate and AliasCall) ----

    @Test
    fun `the transfer does not evaluate call instructions`() {
        val call = AliasInstr.UnresolvedCall(fx.site(9), a.v, listOf(x))
        assertFailsWith<NotImplementedError> { tr.transfer(AliasState.EMPTY, call) }
        val resolved = AliasInstr.ResolvedCall(fx.site(9), a.v, listOf(x))
        assertFailsWith<NotImplementedError> { tr.transfer(AliasState.EMPTY, resolved) }
    }
}
