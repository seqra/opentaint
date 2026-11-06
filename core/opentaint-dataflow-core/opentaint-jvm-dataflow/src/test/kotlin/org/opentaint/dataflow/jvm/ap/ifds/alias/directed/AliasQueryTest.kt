package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.AliasCfg.Node
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

/**
 * Tests of the backward query (IMPL §6.1, §6.3; spec §5.7) on programs of the direct CFG builder.
 * The examples of spec §6 use the arguments `x`, `y`, `z`, `w`, `h`. A query on an argument starts
 * from its root by rule. The last node of each program reads the locals of the query (a probe).
 */
class AliasQueryTest {

    /** One program: the tables, the names of the locals and the arguments, and the query. */
    private class Program(symDepth: Int = 7, val maxAccessors: Int = 6) {
        val fx = DirectedEngineFixture(symDepth)
        val tables get() = fx.tables

        private val localNames = HashMap<Int, String>()
        private val argNames = HashMap<Int, String>()
        private lateinit var cfg: AliasCfg
        lateinit var query: AliasQuery
            private set

        val f = fx.field("f")
        val g = fx.field("g")
        val h = fx.field("h")
        val next = fx.field("next")

        fun local(name: String): AliasValue.Local {
            val l = fx.local(localNames.size)
            localNames[localNames.size] = name
            return l
        }

        fun arg(name: String): AliasValue.Arg {
            val a = fx.arg(argNames.size)
            argNames[argNames.size] = name
            return a
        }

        fun node(instr: AliasInstr, vararg succ: Int, uses: List<AliasValue.Local> = emptyList()) =
            Node(instr, succ, extraUses = uses.map { it.v }.toIntArray())

        fun solve(vararg nodes: Node): Program {
            cfg = AliasCfg.direct(tables, nodes.toList())
            val result = DirectedFixpoint(fx.transfer).run(cfg, verify = true)
            query = AliasQuery(result, maxAccessors)
            return this
        }

        /** `findAlias` of a local or an argument before node [at]. */
        fun aliases(at: Int, v: AliasValue.Ref, after: Boolean = false): Set<String> =
            render(assertNotNull(query.findAlias(at, after, root(v))))

        /** The heap-path query of `v.cells` before node [at]. */
        fun heapAliases(at: Int, v: AliasValue.Ref, vararg cells: CellId): Set<String> =
            render(assertNotNull(query.findHeapAlias(at, false, root(v), cells)))

        fun answer(at: Int, v: AliasValue.Ref): QueryAnswer = assertNotNull(query.findAlias(at, false, root(v)))

        fun root(v: AliasValue.Ref): PathRoot = when (v) {
            is AliasValue.Local -> PathRoot.Var(v.v)
            is AliasValue.Arg -> PathRoot.Base(base(BaseKey.Arg(v.index)))
            AliasValue.This -> PathRoot.Base(base(BaseKey.This))
        }

        private fun base(key: BaseKey): BaseId =
            tables.bases.find(key).also { check(it != NO_ID) { "no base $key" } }

        fun render(answer: QueryAnswer): Set<String> {
            val shown = answer.paths.map { show(it) }
            assertEquals(shown.size, shown.toSet().size, "duplicate paths: $shown")
            return shown.toSortedSet()
        }

        fun show(p: AliasPath): String {
            val root = when (val r = p.root) {
                is PathRoot.Var -> localNames.getValue(assertNotNull(tables.vars.key(r.v)).index)
                is PathRoot.Base -> when (val k = tables.bases.key(r.base)) {
                    BaseKey.This -> "this"
                    is BaseKey.Arg -> argNames.getValue(k.index)
                    is BaseKey.Static -> k.className
                    else -> error("not a root base: $k")
                }
            }
            return root + p.cells.joinToString("") { c ->
                tables.cells.fieldKey(c)?.let { ".${it.fieldName}" } ?: "[*]"
            }
        }
    }

    // Spec §6.1.

    @Test
    fun `spec 6_1 a join relates a to x and to y and not x to y`() {
        val p = Program()
        val x = p.arg("x")
        val y = p.arg("y")
        val a = p.local("a")
        p.solve(
            p.node(AliasInstr.Nop, 1, 2),
            p.node(p.fx.assign(a, x), 3),
            p.node(p.fx.assign(a, y), 3),
            p.node(AliasInstr.Nop, uses = listOf(a)),
        )
        assertEquals(setOf("a"), p.aliases(3, x))
        assertEquals(setOf("a"), p.aliases(3, y))
        assertEquals(setOf("x", "y"), p.aliases(3, a))
    }

    // Spec §6.2.

    @Test
    fun `findAlias of z gives x f y f`() {
        val p = Program()
        val x = p.arg("x")
        val y = p.arg("y")
        val z = p.arg("z")
        val w = p.arg("w")
        val a = p.local("a")
        p.solve(
            p.node(AliasInstr.Nop, 1, 2),
            p.node(p.fx.assign(a, x), 3),
            p.node(p.fx.assign(a, y), 3),
            p.node(p.fx.store(a, p.f, z), 4),
            p.node(p.fx.assign(a, w), 5),
            p.node(AliasInstr.Nop, uses = listOf(a)),
        )
        assertEquals(setOf("x.f", "y.f"), p.aliases(5, z))
        assertEquals(emptySet(), p.aliases(5, x))
        assertEquals(setOf("a"), p.aliases(5, w))
        // A heap-path query: its start set is H(<x>, f) = {<x.f>, <z>}.
        assertEquals(setOf("y.f", "z"), p.heapAliases(5, x, p.f))
    }

    // Spec §6.3.

    @Test
    fun `spec 6_3 a strong update replaces the content of the cell`() {
        val p = Program()
        val x = p.arg("x")
        val z = p.arg("z")
        val b = p.local("b")
        val t = p.local("t")
        p.solve(
            p.node(p.fx.load(b, x, p.f), 1),
            p.node(p.fx.store(x, p.f, z), 2),
            p.node(p.fx.load(t, x, p.f), 3),
            p.node(AliasInstr.Nop, uses = listOf(b, t)),
        )
        assertEquals(setOf("x.f", "z"), p.aliases(3, t))
        assertEquals(emptySet(), p.aliases(3, b))
    }

    @Test
    fun `spec 6_3 a strong update in a loop keeps only the last value of the new object`() {
        val p = Program()
        val x = p.arg("x")
        val y = p.arg("y")
        val n = p.local("n")
        p.solve(
            p.node(AliasInstr.Nop, 1, 5),
            p.node(p.fx.assign(n, AliasValue.New(p.fx.site(1))), 2),
            p.node(p.fx.store(n, p.f, x), 3),
            p.node(p.fx.store(n, p.f, y), 4),
            p.node(AliasInstr.Nop, 0, uses = listOf(n)),
            p.node(AliasInstr.Nop),
        )
        assertTrue(p.tables.sites.isLoopSite(p.fx.site(1)))
        assertTrue("n.f" in p.aliases(4, y))
        assertFalse("n.f" in p.aliases(4, x))
        assertEquals(setOf("y"), p.heapAliases(4, n, p.f))
    }

    // Spec §6.4.

    @Test
    fun `spec 6_4 a read through a join aliases both default cells`() {
        val p = Program()
        val x = p.arg("x")
        val y = p.arg("y")
        val a = p.local("a")
        val t = p.local("t")
        p.solve(
            p.node(AliasInstr.Nop, 1, 2),
            p.node(p.fx.assign(a, x), 3),
            p.node(p.fx.assign(a, y), 3),
            p.node(p.fx.load(t, a, p.f), 4),
            p.node(AliasInstr.Nop, uses = listOf(a, t)),
        )
        assertEquals(setOf("a.f", "x.f", "y.f"), p.aliases(4, t))
    }

    // Spec §6.5.

    @Test
    fun `spec 6_5 a list loop relates x to x next and to h but not h to h next`() {
        val p = Program(symDepth = 2, maxAccessors = 1)
        val h = p.arg("h")
        val x = p.local("x")
        p.solve(
            p.node(p.fx.assign(x, h), 1),
            p.node(AliasInstr.Nop, 2, 3),
            p.node(p.fx.load(x, x, p.next), 1),
            p.node(AliasInstr.Nop, uses = listOf(x)),
        )
        // The cells of the table are [*], f, g, h and next. deep(h) is the default content of each cell
        // of <h.next.next>, so x.c aliases x for each cell c (D = 1).
        assertEquals(setOf("h", "h.next", "x.f", "x.g", "x.h", "x.next", "x[*]"), p.aliases(3, x))
        assertEquals(setOf("x"), p.aliases(3, h))
    }

    @Test
    fun `the search never expands the self cell of a deep origin`() {
        val p = Program(symDepth = 2, maxAccessors = 4)
        val h = p.arg("h")
        val x = p.local("x")
        p.solve(
            p.node(p.fx.assign(x, h), 1),
            p.node(AliasInstr.Nop, 2, 3),
            p.node(p.fx.load(x, x, p.next), 1),
            p.node(AliasInstr.Nop, uses = listOf(x)),
        )
        val answer = p.aliases(3, x)
        // x.next.next.next reads deep(h) through <h.next.next>: found.
        assertTrue("x.next.next.next" in answer, answer.toString())
        assertTrue("h.next.next.next" in answer, answer.toString())
        // x.next.next.next.next needs the self cell (deep(h), next): not followed.
        assertFalse("x.next.next.next.next" in answer, answer.toString())
        assertTrue(answer.all { s -> s.count { it == '.' } + s.count { it == '[' } <= 4 })
    }

    // Spec §6.6.

    @Test
    fun `spec 6_6 a read of a new object aliases its cell and two null sites do not alias`() {
        val p = Program()
        val x = p.local("x")
        val a = p.local("a")
        val pn = p.local("p")
        val q = p.local("q")
        val r = p.local("r")
        p.solve(
            p.node(p.fx.assign(x, AliasValue.New(p.fx.site(0))), 1),
            p.node(p.fx.load(a, x, p.f), 2),
            p.node(p.fx.assign(pn, AliasValue.Null(p.fx.site(2))), 3),
            p.node(p.fx.assign(q, AliasValue.Null(p.fx.site(3))), 4),
            p.node(p.fx.assign(r, pn), 5),
            p.node(AliasInstr.Nop, uses = listOf(x, a, pn, q, r)),
        )
        assertEquals(setOf("x.f"), p.aliases(5, a))
        assertEquals(setOf("r"), p.aliases(5, pn))
        assertEquals(emptySet(), p.aliases(5, q))
    }

    // Spec §6.7.

    @Test
    fun `spec 6_7 a call keeps the cell aliases and a store through a reached value is weak`() {
        val p = Program()
        val x = p.arg("x")
        val y = p.arg("y")
        val z = p.arg("z")
        val w = p.local("w")
        val u = p.local("u")
        val v = p.local("v")
        p.solve(
            p.node(p.fx.load(w, x, p.f), 1),
            p.node(AliasInstr.UnresolvedCall(p.fx.site(1), null, listOf(x)), 2),
            p.node(p.fx.load(u, x, p.f), 3),
            p.node(p.fx.load(v, y, p.g), 4),
            p.node(p.fx.store(u, p.h, z), 5),
            p.node(AliasInstr.Nop, uses = listOf(w, u, v)),
        )
        assertEquals(setOf("w", "x.f"), p.aliases(5, u))
        // The weak store keeps the default <x.f.h> and adds <z>.
        assertEquals(setOf("u.h", "w.h", "x.f.h"), p.aliases(5, z))
    }

    @Test
    fun `spec 6_7 the readers of a cell of a reached new object alias after a call`() {
        val p = Program()
        val n = p.local("n")
        val a = p.local("a")
        val b = p.local("b")
        val c = p.local("c")
        val d = p.local("d")
        p.solve(
            p.node(p.fx.assign(n, AliasValue.New(p.fx.site(0))), 1),
            p.node(p.fx.store(n, p.g, AliasValue.Null(p.fx.site(1))), 2),
            p.node(AliasInstr.UnresolvedCall(p.fx.site(2), null, listOf(n)), 3),
            p.node(p.fx.load(a, n, p.f), 4),
            p.node(p.fx.load(b, n, p.f), 5),
            p.node(p.fx.load(c, n, p.g), 6),
            p.node(p.fx.load(d, n, p.g), 7),
            p.node(AliasInstr.Nop, uses = listOf(n, a, b, c, d)),
        )
        assertEquals(setOf("b", "n.f"), p.aliases(7, a))
        assertEquals(setOf("d", "n.g"), p.aliases(7, c))
    }

    // Spec §6.8.

    @Test
    fun `spec 6_8 two reads of a static field alias and the static write is ignored`() {
        val p = Program()
        val t = p.local("t")
        val u = p.local("u")
        p.solve(
            p.node(AliasInstr.StaticWrite, 1),
            p.node(p.fx.staticRead(t, "C", p.f), 2),
            p.node(p.fx.staticRead(u, "C", p.f), 3),
            p.node(AliasInstr.Nop, uses = listOf(t, u)),
        )
        // The ignored write `C.f = v` gives no alias of t.
        assertEquals(setOf("C.f", "u"), p.aliases(3, t))
    }

    // The universe of the search (ruling of the Task 5 review).

    /** K = 2: `t = x.f; y = x; while (c) y = y.next`. y holds deep(x). t is local 0 and y is local 1. */
    private fun deepLoopWithField(): Program {
        val p = Program(symDepth = 2, maxAccessors = 3)
        val x = p.arg("x")
        val t = p.local("t")
        val y = p.local("y")
        p.solve(
            p.node(p.fx.load(t, x, p.f), 1),
            p.node(p.fx.assign(y, x), 2),
            p.node(AliasInstr.Nop, 3, 4),
            p.node(p.fx.load(y, y, p.next), 2),
            p.node(AliasInstr.Nop, uses = listOf(t, y)),
        )
        return p
    }

    @Test
    fun `the default parents of a deep origin are only the depth K origins of the table`() {
        val p = deepLoopWithField()
        val y = AliasValue.Local(p.tables.vars.find(Y_LOCAL))
        val answer = p.aliases(4, y)
        assertTrue("x" in answer && "y.next" in answer, answer.toString())
        // Ruling of the Task 5 review: the Lean search also gives t.g.c (for each cell c) through the
        // depth-K origin <x.f.g>, the default parent of deep(x). No state holds <x.f.g>, so it is not
        // in the universe. By A1 it is not an object that deep(x) stands for: no real alias is lost.
        assertTrue(answer.none { it.startsWith("t.") }, answer.toString())
    }

    @Test
    fun `query-local origins of a heap query do not change a later findAlias`() {
        val p = deepLoopWithField()
        val x = AliasValue.Arg(0)
        val t = AliasValue.Local(p.tables.vars.find(T_LOCAL))
        val y = AliasValue.Local(p.tables.vars.find(Y_LOCAL))
        // These heap queries make query-local origins: <x.f.g>, <x.f.g.h> (deep(x)), <x.h>, <x.h.g>.
        p.heapAliases(4, t, p.g, p.h)
        p.heapAliases(4, x, p.h, p.g)
        p.query.findArrayElementAliases(4, false, p.root(t))
        val fresh = deepLoopWithField()
        val freshT = AliasValue.Local(fresh.tables.vars.find(T_LOCAL))
        val freshY = AliasValue.Local(fresh.tables.vars.find(Y_LOCAL))
        assertEquals(fresh.aliases(4, freshY), p.aliases(4, y))
        assertEquals(fresh.aliases(4, freshT), p.aliases(4, t))
        assertEquals(fresh.aliases(4, AliasValue.Arg(0)), p.aliases(4, x))
    }

    // Query-local defaults (IMPL §6.4).

    @Test
    fun `a heap path query reads default cells that the analysis did not make`() {
        val p = Program()
        val x = p.arg("x")
        val t = p.local("t")
        p.solve(
            p.node(p.fx.assign(t, x), 1),
            p.node(AliasInstr.Nop, uses = listOf(t)),
        )
        val originsBefore = p.tables.origins.size
        val nodesBefore = p.tables.nodes.nodeCount
        assertEquals(setOf("x.f.g"), p.heapAliases(1, t, p.f, p.g))
        assertEquals(setOf("t.f.g"), p.heapAliases(1, x, p.f, p.g))
        assertEquals(originsBefore, p.tables.origins.size)
        assertEquals(nodesBefore, p.tables.nodes.nodeCount)
    }

    @Test
    fun `a heap path query below depth K reads a query-local deep origin`() {
        val p = Program(symDepth = 1)
        val x = p.arg("x")
        val t = p.local("t")
        p.solve(
            p.node(p.fx.load(t, x, p.f), 1),
            p.node(AliasInstr.Nop, uses = listOf(t)),
        )
        // t.g holds deep(x). deep(x) is the default content of each cell of <x.f>.
        assertEquals(
            setOf("t.f", "t.h", "t.next", "t[*]", "x.f.f", "x.f.g", "x.f.h", "x.f.next", "x.f[*]"),
            p.heapAliases(1, t, p.g),
        )
    }

    @Test
    fun `a query-local deep origin has the query-local origins at depth K as default parents`() {
        val p = Program(symDepth = 1)
        val x = p.arg("x")
        val t = p.local("t")
        p.solve(
            p.node(p.fx.assign(t, x), 1),
            p.node(AliasInstr.Nop, uses = listOf(t)),
        )
        // <x.f> and deep(x) are query-local. deep(x) is the default content of each cell of <x.f>.
        assertEquals(
            setOf("t.f.f", "t.f.h", "t.f.next", "t.f[*]", "x.f.f", "x.f.g", "x.f.h", "x.f.next", "x.f[*]"),
            p.heapAliases(1, t, p.f, p.g),
        )
    }

    @Test
    fun `a cell of an allocation child has the new and the old object as default parents`() {
        val p = Program()
        val n = p.local("n")
        val prev = p.local("prev")
        val a = p.local("a")
        p.solve(
            p.node(AliasInstr.Nop, 1, 5),
            p.node(p.fx.assign(prev, n), 2),
            p.node(p.fx.assign(n, AliasValue.New(p.fx.site(2))), 3),
            p.node(p.fx.load(a, n, p.f), 4),
            p.node(AliasInstr.Nop, 0, uses = listOf(prev, n, a)),
            p.node(AliasInstr.Nop),
        )
        // prev holds old(2) and n holds new(2). Both cells f hold their default <@2.f>.
        assertEquals(setOf("n.f", "prev.f"), p.aliases(4, a))
    }

    @Test
    fun `an array element query starts from the element value of the array`() {
        val p = Program()
        val x = p.arg("x")
        val arr = p.local("arr")
        val e = p.local("e")
        p.solve(
            p.node(p.fx.assign(arr, AliasValue.New(p.fx.site(0))), 1),
            p.node(p.fx.astore(arr, x), 2),
            p.node(p.fx.aload(e, arr), 3),
            p.node(AliasInstr.Nop, uses = listOf(arr, e)),
        )
        val answer = assertNotNull(p.query.findArrayElementAliases(3, false, p.root(arr)))
        assertEquals(setOf("e", "x"), p.render(answer))
        val news = p.tables.origins.allocNew(p.fx.site(0))
        val elem = p.tables.origins.findChild(news, ELEM_CELL)
        assertEquals(setOf(elem, p.fx.argO(0)), answer.seeds.toSet())
    }

    @Test
    fun `the answer is the same for the state after a statement`() {
        val p = Program()
        val x = p.arg("x")
        val t = p.local("t")
        p.solve(
            p.node(p.fx.load(t, x, p.f), 1),
            p.node(AliasInstr.Nop, uses = listOf(t)),
        )
        assertEquals(setOf("x.f"), p.aliases(0, t, after = true))
        assertEquals(setOf("x.f"), p.aliases(1, t))
    }

    @Test
    fun `a node without a state has no answer`() {
        val p = Program()
        val x = p.arg("x")
        val t = p.local("t")
        p.solve(
            p.node(p.fx.load(t, x, p.f)),
            p.node(AliasInstr.Nop, uses = listOf(t)),
        )
        assertNull(p.query.findAlias(1, false, p.root(t)))
        assertNull(p.query.findHeapAlias(1, true, p.root(t), intArrayOf(p.f)))
    }

    @Test
    fun `a query does not change the tables`() {
        val p = Program()
        val x = p.arg("x")
        val t = p.local("t")
        p.solve(
            p.node(p.fx.load(t, x, p.f), 1),
            p.node(AliasInstr.Nop, uses = listOf(t)),
        )
        val originsBefore = p.tables.origins.size
        val nodesBefore = p.tables.nodes.nodeCount
        repeat(2) {
            p.aliases(1, t)
            p.aliases(1, x)
            p.heapAliases(1, t, p.g, p.h, p.next)
            p.query.findArrayElementAliases(1, false, p.root(x))
        }
        assertEquals(originsBefore, p.tables.origins.size)
        assertEquals(nodesBefore, p.tables.nodes.nodeCount)
    }

    private companion object {
        const val T_LOCAL = 0
        const val Y_LOCAL = 1
    }
}
