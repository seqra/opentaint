package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.AliasCfg.Node
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/**
 * Tests of the unresolved call (IMPL §4.4, §4.5; spec §5.6, §6.7): the closure over the written
 * cells, the filters of `Etree` and `Eval`, the markers, the budget, and the pass-through models.
 */
class AliasCallTest {

    private val fx = DirectedEngineFixture()
    private val fp = DirectedFixpoint(fx.transfer)
    private val origins = fx.origins
    private val bases = fx.bases
    private val nodes = fx.nodes

    private val f = fx.field("f")
    private val g = fx.field("g")
    private val h = fx.field("h")
    private val box = fx.field("box")
    private val value = fx.field("value")

    private val x = fx.arg(0)
    private val y = fx.arg(1)
    private val z = fx.arg(2)
    private val w = fx.local(0)
    private val e = fx.local(1)
    private val t = fx.local(2)
    private val u = fx.local(3)
    private val v = fx.local(4)
    private val n = fx.local(5)
    private val a = fx.local(6)
    private val b = fx.local(7)
    private val c = fx.local(8)
    private val d = fx.local(9)
    private val r = fx.local(10)

    /** Runs [instrs] as a straight-line CFG and checks the post-fixpoint conditions ([DirectedTestDriver.runStraight]). */
    private fun run(vararg instrs: AliasInstr, fixpoint: DirectedFixpoint = fp, from: AliasState = AliasState.EMPTY): AliasState =
        DirectedTestDriver.runStraight(fixpoint, fx.tables, instrs.toList(), from)

    private fun call(
        site: Int,
        vararg args: AliasValue,
        result: AliasValue.Local? = null,
        models: List<PassThrough> = emptyList(),
    ) = AliasInstr.UnresolvedCall(fx.site(site), result?.v, args.toList(), models)

    private fun newO(site: Int) = origins.allocNew(fx.site(site))
    private fun oldO(site: Int) = origins.allocOld(fx.site(site))
    private fun freshO(site: Int) = origins.root(bases.fresh(fx.site(site)))
    private fun nullO(site: Int) = origins.root(bases.nullAt(fx.site(site)))
    private fun childO(site: Int, cell: CellId) = origins.child(newO(site), cell)
    private fun staticO(cls: String) = origins.root(bases.static(cls))

    private fun etree(st: AliasState): Set<OriginId> = nodes.members(st.varNode(ETREE)).toSet()
    private fun eval(st: AliasState): Set<OriginId> = nodes.members(st.varNode(EVAL)).toSet()
    private fun pts(st: AliasState, l: AliasValue.Ref) = fx.pts(st, l)

    private val statics = OriginTable.REACHED_STATICS

    // Spec §6.7.

    @Test
    fun `spec 6_7 a call reaches the argument and a store through a value of a reached cell is weak`() {
        val before = run(fx.load(w, x, f))
        val after = run(call(9, x), from = before)
        assertEquals(fx.set(fx.argO(0), statics), etree(after))
        // The cell (x, f) is not written: the engine Eval is empty; <x.f> is blocked by its prefix <x>.
        assertEquals(emptySet(), eval(after))
        assertEquals(before.heap, after.heap)

        val st = run(fx.load(u, x, f), fx.load(v, y, g), fx.store(u, h, z), from = after)
        val xf = fx.path(fx.argO(0), f)
        assertEquals(fx.set(xf), pts(st, w))
        assertEquals(fx.set(xf), pts(st, u))
        assertEquals(fx.set(fx.path(fx.argO(1), g)), pts(st, v))
        assertEquals(fx.set(fx.path(xf, h), fx.argO(2)), fx.cell(st, xf, h))
    }

    @Test
    fun `spec 6_7 a new object and an explicit null keep their cell names after a call`() {
        val st = run(
            fx.assign(n, AliasValue.New(fx.site(5))),
            fx.store(n, g, AliasValue.Null(fx.site(0))),
            call(9, n),
        )
        assertEquals(fx.set(nullO(0)), fx.cell(st, newO(5), g))
        assertEquals(fx.set(statics, nullO(0)), etree(st))
        assertEquals(emptySet(), eval(st))
        val end = run(fx.load(a, n, f), fx.load(b, n, f), fx.load(c, n, g), fx.load(d, n, g), from = st)
        assertEquals(fx.set(childO(5, f)), pts(end, a))
        assertEquals(pts(end, a), pts(end, b))
        assertEquals(fx.set(nullO(0)), pts(end, c))
        assertEquals(pts(end, c), pts(end, d))
    }

    // Spec §5.6 examples.

    @Test
    fun `spec 5_6 two reads of a cell of a reached new object alias`() {
        val st = run(fx.assign(n, AliasValue.New(fx.site(5))), call(6, n), fx.load(a, n, f), fx.load(b, n, f))
        assertEquals(fx.set(childO(5, f)), pts(st, a))
        assertEquals(pts(st, a), pts(st, b))
    }

    @Test
    fun `spec 5_6 a reached prefix makes the store weak and w g keeps e`() {
        val st = run(
            fx.load(w, x, f), fx.load(e, w, g),
            call(9, x),
            fx.load(t, x, f), fx.store(t, g, z),
        )
        val xf = fx.path(fx.argO(0), f)
        assertEquals(fx.set(fx.path(xf, g)), pts(st, e))
        assertEquals(fx.set(fx.path(xf, g), fx.argO(2)), fx.cell(st, xf, g))
        assertTrue(pts(st, e).all { it in fx.cell(st, xf, g) })
    }

    @Test
    fun `spec 5_6 a value of a reached cell is in Eval and the store through it is weak`() {
        val zz = fx.local(11)
        val st = run(
            fx.assign(zz, AliasValue.New(fx.site(0))),
            fx.store(zz, g, y),
            fx.store(x, f, zz),
            call(9, x),
        )
        assertEquals(fx.set(newO(0), fx.argO(1)), eval(st))
        assertEquals(fx.set(fx.argO(0), fx.argO(1), statics), etree(st))
        val end = run(fx.load(t, x, f), fx.store(t, g, z), from = st)
        assertEquals(fx.set(newO(0)), pts(end, t))
        assertEquals(fx.set(fx.argO(1), fx.argO(2)), fx.cell(end, newO(0), g))
    }

    @Test
    fun `spec 5_6 a call without arguments does not reach this`() {
        val st = run(fx.load(t, AliasValue.This, box), call(1), fx.store(t, value, z))
        val tb = fx.path(fx.thisO(), box)
        assertEquals(fx.set(fx.argO(2)), fx.cell(st, tb, value))
    }

    // Losses L1 and L4 (IMPL §1.4).

    @Test
    fun `loss L1 a store through a value read before a call on its holder is weak`() {
        val st = run(fx.load(t, x, f), call(1, x), fx.store(t, g, z))
        val xf = fx.path(fx.argO(0), f)
        assertEquals(fx.set(fx.path(xf, g), fx.argO(2)), fx.cell(st, xf, g))
    }

    @Test
    fun `loss L4 a store through a value found in a reached cell is weak`() {
        val st = run(
            fx.assign(b, AliasValue.New(fx.site(0))),
            fx.store(AliasValue.This, box, b),
            call(2, AliasValue.This),
            fx.store(b, value, z),
        )
        assertEquals(fx.set(newO(0)), fx.cell(st, fx.thisO(), box))
        assertEquals(fx.set(childO(0, value), fx.argO(2)), fx.cell(st, newO(0), value))
    }

    // Heap, markers, budget.

    @Test
    fun `call writes no heap entry`() {
        val before = run(
            fx.assign(n, AliasValue.New(fx.site(0))),
            fx.store(n, f, x),
            fx.store(x, g, n),
            fx.store(y, f, AliasValue.Null(fx.site(1))),
        )
        val after = run(call(2, x, y, n, result = r), from = before)
        assertEquals(before.heap, after.heap)
        before.forEachVar { k, node -> assertEquals(node, after.varNode(k), "env $k") }
        after.forEachVar { k, _ ->
            if (k != ETREE && k != EVAL && k != r.v) assertEquals(before.varNode(k), after.varNode(k), "env $k")
        }
        assertEquals(fx.set(freshO(2)), pts(after, r))
    }

    @Test
    fun `closure over budget blocks all strong updates`() {
        val small = DirectedFixpoint(fx.transfer, maxCallClosure = 3)
        val prog = arrayOf(
            fx.store(x, f, y),
            fx.store(x, g, z),
            call(1, x),
            fx.assign(n, AliasValue.New(fx.site(2))),
            fx.store(n, f, z),
            fx.store(fx.arg(3), f, z),
        )
        val st = run(*prog, fixpoint = small)
        assertTrue(OriginTable.REACHED_ALL in etree(st))
        assertTrue(OriginTable.REACHED_ALL in eval(st))
        assertEquals(fx.set(childO(2, f), fx.argO(2)), fx.cell(st, newO(2), f))
        assertEquals(fx.set(fx.path(fx.argO(3), f), fx.argO(2)), fx.cell(st, fx.argO(3), f))

        // The same program with the default budget: the closure is {x, y, z, REACHED_STATICS}.
        val ok = run(*prog)
        assertEquals(fx.set(fx.argO(0), fx.argO(1), fx.argO(2), statics), etree(ok))
        assertEquals(fx.set(fx.argO(2)), fx.cell(ok, newO(2), f))
        assertEquals(fx.set(fx.argO(2)), fx.cell(ok, fx.argO(3), f))
    }

    @Test
    fun `REACHED_STATICS blocks a store below a static read after a call`() {
        val z1 = AliasValue.Const(bases.const(STRING_TYPE, "z1"))
        val z2 = AliasValue.Const(bases.const(STRING_TYPE, "z2"))
        val cf = fx.path(staticO("C"), f)
        val beforeCall = run(fx.staticRead(t, "C", f), fx.store(t, g, z1))
        assertEquals(fx.set(origins.root(z1.base)), fx.cell(beforeCall, cf, g))
        val st = run(call(1), fx.store(t, g, z2), from = beforeCall)
        assertTrue(statics in etree(st))
        // The written cell (<C.f>, g) is covered by REACHED_STATICS: its content is reached.
        assertTrue(origins.root(z1.base) in etree(st))
        assertEquals(fx.set(origins.root(z1.base), origins.root(z2.base)), fx.cell(st, cf, g))
    }

    @Test
    fun `a store on an object that the call did not reach stays strong`() {
        val st = run(
            fx.assign(n, AliasValue.New(fx.site(0))),
            call(1, x),
            fx.store(y, f, z),
            fx.store(n, f, z),
        )
        assertEquals(fx.set(fx.argO(2)), fx.cell(st, fx.argO(1), f))
        assertEquals(fx.set(fx.argO(2)), fx.cell(st, newO(0), f))
    }

    @Test
    fun `Etree keeps symbolic origins and markers and Eval keeps contents that can be unique`() {
        val loop = fx.loopSite(20)
        val st0 = run(
            fx.assign(n, AliasValue.New(fx.site(0))),
            fx.store(x, f, n),                                  // AllocNew: Eval
            fx.store(x, g, AliasValue.Null(fx.site(1))),        // null: not unique
            fx.store(x, h, AliasValue.Const(bases.const(STRING_TYPE, "s"))),
            fx.store(n, f, AliasValue.Fresh(loop)),             // fresh of a loop site: not unique
            fx.store(n, g, y),                                  // entry root: Eval
        )
        val st = run(call(2, x), from = st0)
        val constO = origins.root(bases.const(STRING_TYPE, "s"))
        val loopFresh = origins.root(bases.fresh(loop))
        assertEquals(fx.set(fx.argO(0), fx.argO(1), statics, nullO(1), constO, loopFresh), etree(st))
        assertEquals(fx.set(newO(0), fx.argO(1)), eval(st))
    }

    // Coverage of the heap index.

    @Test
    fun `a written cell below a reached origin is covered by its ancestor`() {
        // t = x.f.g; t.h = y (strong: no call yet); m(x): <x> covers the written cell (<x.f.g>, h).
        val st0 = run(fx.load(t, x, f), fx.load(t, t, g), fx.store(t, h, y))
        val xfg = fx.path(fx.argO(0), f, g)
        assertEquals(fx.set(fx.argO(1)), fx.cell(st0, xfg, h))
        val st = run(call(1, x), from = st0)
        assertEquals(fx.set(fx.argO(0), fx.argO(1), statics), etree(st))
        assertEquals(fx.set(fx.argO(1)), eval(st))
        // A call on <x.f.g> itself covers it too; a call on <x.g> does not.
        assertTrue(fx.argO(1) in etree(run(call(2, t), from = st0)))
        val other = run(fx.load(u, x, g), call(3, u), from = st0)
        assertTrue(fx.argO(1) !in etree(other))
    }

    @Test
    fun `a written cell of a deep origin is covered by a symbolic origin of its base`() {
        val k1 = DirectedEngineFixture(symDepth = 1)
        val kfp = DirectedFixpoint(k1.transfer)
        val lx = k1.arg(0)
        val tt = k1.local(0)
        val uu = k1.local(1)
        val ff = k1.field("f")
        val gg = k1.field("g")
        val st0 = listOf(
            k1.load(tt, lx, ff),     // <x.f>
            k1.load(uu, tt, gg),     // deep(x)
            k1.store(uu, ff, k1.arg(1)),
        ).fold(AliasState.EMPTY) { s, i -> kfp.evaluate(s, i) }
        val deep = k1.origins.deep(k1.bases.arg(0))
        assertEquals(setOf(deep), k1.pts(st0, uu))
        assertTrue(k1.argO(1) in k1.cell(st0, deep, ff))
        val st = kfp.evaluate(st0, AliasInstr.UnresolvedCall(k1.site(5), null, listOf(lx)))
        val et = k1.nodes.members(st.varNode(ETREE)).toSet()
        assertTrue(k1.argO(1) in et, "content of the deep cell is reached: $et")
        // A call on another root does not cover deep(x).
        val other = kfp.evaluate(st0, AliasInstr.UnresolvedCall(k1.site(6), null, listOf(k1.arg(2))))
        assertTrue(k1.argO(1) !in k1.nodes.members(other.varNode(ETREE)).toSet())
    }

    @Test
    fun `a written cell of an allocation child is covered by the new and the old object of its site`() {
        val loop = fx.loopSite(30)
        // n = new (loop site); c = n.f; c.g = y (weak: <@s.f> is not unique).
        val st0 = run(fx.assign(n, AliasValue.New(loop)), fx.load(c, n, f), fx.store(c, g, y))
        val cf = origins.child(origins.allocNew(loop), f)
        assertTrue(fx.argO(1) in fx.cell(st0, cf, g))
        val reachedNew = run(call(31, n), from = st0)
        assertTrue(fx.argO(1) in etree(reachedNew))
        assertTrue(fx.argO(1) in eval(reachedNew))

        // After a retire, n holds the old object only; the old object covers the same child.
        val retired = run(fx.assign(a, AliasValue.New(loop)), from = st0)
        assertEquals(fx.set(origins.allocOld(loop)), pts(retired, n))
        val reachedOld = run(call(32, n), from = retired)
        assertTrue(fx.argO(1) in etree(reachedOld))
        // The child names the cell of each object of the site: the new object after the retire covers it too.
        val reachedNext = run(fx.assign(n, AliasValue.Null(fx.site(33))), call(34, a), from = retired)
        assertTrue(fx.argO(1) in etree(reachedNext))
        // A call on another object does not cover it.
        val notReached = run(fx.assign(n, AliasValue.Null(fx.site(35))), call(36, x), from = retired)
        assertTrue(fx.argO(1) !in etree(notReached))
    }

    @Test
    fun `resolved call without a callee body uses the unresolved call rule`() {
        val st0 = run(fx.store(x, f, y))
        val un = run(call(1, x, result = r), from = st0)
        val res = run(AliasInstr.ResolvedCall(fx.site(1), r.v, listOf(x)), from = st0)
        assertEquals(un, res)
    }

    @Test
    fun `closure agrees with a naive closure over the written cells on random states`() {
        val k = DirectedEngineFixture(symDepth = 2)
        val kfp = DirectedFixpoint(k.transfer)
        val ko = k.origins
        val kb = k.bases
        val cells = listOf(k.field("f"), k.field("g"), ELEM_CELL)
        val loop = k.loopSite(40)
        val plain = k.site(41)
        val universe = buildList {
            for (i in 0..2) {
                val root = k.argO(i)
                add(root)
                for (c1 in cells) {
                    val p1 = ko.child(root, c1)
                    add(p1)
                    for (c2 in cells) add(ko.child(p1, c2))
                }
                add(ko.deep(kb.arg(i)))
            }
            val st = ko.root(kb.static("S"))
            add(st)
            add(ko.child(st, cells[0]))
            add(ko.child(ko.child(st, cells[0]), cells[1]))
            for (s in listOf(loop, plain)) {
                add(ko.allocNew(s))
                add(ko.allocOld(s))
                val ch = ko.child(ko.allocNew(s), cells[0])
                add(ch)
                add(ko.child(ch, cells[1]))
                add(ko.deep(kb.allocChild(s, cells[0])))
            }
            add(ko.root(kb.fresh(plain)))
            add(ko.root(kb.fresh(loop)))
            add(ko.root(kb.nullAt(plain)))
            add(ko.root(kb.const(STRING_TYPE, "k")))
        }.distinct()

        fun descNaive(aO: OriginId, uO: OriginId): Boolean {
            if (aO == uO) return true
            if (aO == OriginTable.REACHED_STATICS) return ko.baseKind(uO) == BaseKind.STATIC
            if (ko.isSym(aO) && ko.isSym(uO)) return ko.base(aO) == ko.base(uO) && ko.isProperAncestor(aO, uO)
            if (ko.isSym(aO) && ko.isDeep(uO)) return ko.base(aO) == ko.base(uO)
            if (ko.isAlloc(aO) && (ko.isSym(uO) || ko.isDeep(uO))) {
                val key = kb.key(ko.base(uO))
                return key is BaseKey.AllocChild && key.site == ko.site(aO)
            }
            return false
        }

        repeat(60) { seed ->
            val rnd = Random(seed)
            val ed = k.transfer.edit(AliasState.EMPTY)
            repeat(rnd.nextInt(1, 14)) {
                val o = universe[rnd.nextInt(universe.size)]
                val cell = cells[rnd.nextInt(cells.size)]
                val content = List(rnd.nextInt(1, 4)) { universe[rnd.nextInt(universe.size)] }.distinct().sorted()
                val node = k.nodes.intern(content.toIntArray())
                if (node != ko.defaultNode(o, cell)) ed.setHeap(heapKey(o, cell), node)
            }
            if (rnd.nextBoolean()) ed.setVar(ETREE, k.nodes.singleton(universe[rnd.nextInt(universe.size)]))
            if (rnd.nextBoolean()) ed.setVar(EVAL, k.nodes.singleton(universe[rnd.nextInt(universe.size)]))
            val st = ed.build()
            val roots = List(rnd.nextInt(0, 3)) { universe[rnd.nextInt(universe.size)] }.distinct().sorted()
            val rootNode = k.nodes.intern(roots.toIntArray())

            // The naive closure: repeat over all written keys until R does not grow.
            val reached = (roots + OriginTable.REACHED_STATICS).toMutableSet()
            var grew = true
            while (grew) {
                grew = false
                st.forEachHeap { key, node ->
                    if (reached.any { descNaive(it, heapKeyOrigin(key)) }) {
                        for (o in k.nodes.members(node)) if (reached.add(o)) grew = true
                    }
                }
            }
            val vals = mutableSetOf<OriginId>()
            st.forEachHeap { key, node ->
                if (reached.any { descNaive(it, heapKeyOrigin(key)) }) {
                    for (o in k.nodes.members(node)) if (ko.uniqueByKind(o)) vals.add(o)
                }
            }
            val expectedTree = k.nodes.members(st.varNode(ETREE)).toSet() + reached.filter { ko.isSym(it) || ko.isMarker(it) }
            val expectedVal = k.nodes.members(st.varNode(EVAL)).toSet() + vals

            val res = kfp.calls.call(st, rootNode)
            assertEquals(expectedTree, k.nodes.members(res.varNode(ETREE)).toSet(), "Etree, seed $seed")
            assertEquals(expectedVal, k.nodes.members(res.varNode(EVAL)).toSet(), "Eval, seed $seed")
            assertEquals(st.heap, res.heap, "heap, seed $seed")
        }
    }

    // Pass-through models (IMPL §4.5).

    private fun at(base: AliasValue, vararg cells: CellId) = ModelPath(ModelBase.Value(base), cells.toList())
    private val result = ModelPath(ModelBase.Result)

    @Test
    fun `pass-through model from arg0 to result is a weak copy into the result`() {
        val st = run(fx.assign(a, x), call(1, a, result = r, models = listOf(PassThrough(at(a), result))))
        assertEquals(fx.set(freshO(1), fx.argO(0)), pts(st, r))
    }

    @Test
    fun `pass-through model to arg0 f is a weak store`() {
        val st = run(
            fx.assign(a, x), fx.assign(b, y),
            call(1, a, b, models = listOf(PassThrough(at(b), at(a, f)))),
        )
        assertEquals(fx.set(fx.path(fx.argO(0), f), fx.argO(1)), fx.cell(st, fx.argO(0), f))
    }

    @Test
    fun `pass-through model to a path stores into the cell of the loaded base`() {
        val st = run(
            fx.assign(a, x),
            call(1, a, y, models = listOf(PassThrough(at(y), at(a, f, g)))),
        )
        val xf = fx.path(fx.argO(0), f)
        assertEquals(fx.set(fx.path(xf, g), fx.argO(1)), fx.cell(st, xf, g))
    }

    @Test
    fun `pass-through model to a local without accessors adds to the local`() {
        val st = run(fx.assign(a, x), call(1, a, y, models = listOf(PassThrough(at(y), at(a)))))
        assertEquals(fx.set(fx.argO(0), fx.argO(1)), pts(st, a))
    }

    @Test
    fun `pass-through model reads its source in the state before the call`() {
        // Model 1 writes y into a.f; model 2 reads a.f: it gets the content before the call.
        val st = run(
            fx.assign(a, x),
            call(
                1, a, y, result = r,
                models = listOf(PassThrough(at(y), at(a, f)), PassThrough(at(a, f), result)),
            ),
        )
        assertEquals(fx.set(freshO(1), fx.path(fx.argO(0), f)), pts(st, r))
        assertEquals(fx.set(fx.path(fx.argO(0), f), fx.argO(1)), fx.cell(st, fx.argO(0), f))
    }

    @Test
    fun `pass-through model from the result reads the state after the call`() {
        val st = run(fx.assign(a, x), call(1, a, result = r, models = listOf(PassThrough(result, at(a, f)))))
        assertEquals(fx.set(fx.path(fx.argO(0), f), freshO(1)), fx.cell(st, fx.argO(0), f))
    }

    @Test
    fun `pass-through model on the result of a call without a result variable is skipped`() {
        val before = run(fx.assign(a, x))
        val st = run(call(1, a, models = listOf(PassThrough(result, at(a, f)), PassThrough(at(a), result))), from = before)
        assertEquals(before.heap, st.heap)
    }

    @Test
    fun `pass-through model to this without accessors changes nothing`() {
        val before = run(fx.assign(a, x))
        val st = run(call(1, AliasValue.This, a, models = listOf(PassThrough(at(a), at(AliasValue.This)))), from = before)
        assertEquals(fx.set(fx.thisO()), pts(st, AliasValue.This))
        assertEquals(fx.set(fx.argO(0)), pts(st, a))
        assertEquals(before.heap, st.heap)
    }

    @Test
    fun `a model call with a handler passes the post-fixpoint check`() {
        val g1 = AliasCfg.direct(
            fx.tables,
            listOf(
                Node(fx.assign(a, x), intArrayOf(1)),
                Node(call(1, a, y, result = r, models = listOf(PassThrough(at(y), at(a, f)), PassThrough(at(a), result))),
                    intArrayOf(2), exc = intArrayOf(3)),
                Node(AliasInstr.Return(r)),
                Node(fx.load(t, a, f), intArrayOf(4)),
                Node(AliasInstr.Return(t)),
            ),
        )
        val states = fp.solve(g1)
        assertEquals(emptyList(), PostFixChecker(fp).check(g1, states))
        val handler = states.statesBefore[3]!!
        assertTrue(fx.argO(0) in etree(handler))
        assertTrue(fx.argO(1) in fx.cell(handler, fx.argO(0), f))
    }
}
