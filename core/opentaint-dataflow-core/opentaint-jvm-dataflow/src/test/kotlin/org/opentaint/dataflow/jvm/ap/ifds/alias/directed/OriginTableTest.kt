package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import kotlin.test.Test
import kotlin.test.assertContentEquals
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertNotEquals
import kotlin.test.assertTrue

class OriginTableTest {

    private val tables = AliasTables(symDepth = 2)
    private val origins = tables.origins
    private val bases = tables.bases
    private val nodes = tables.nodes
    private val f = tables.cells.field("C", "f", "java.lang.Object")
    private val g = tables.cells.field("C", "g", "java.lang.Object")

    private fun defaultKeys(o: OriginId, c: CellId): List<OriginKey> =
        nodes.members(origins.defaultNode(o, c)).map { origins.key(it) }

    @Test
    fun `reserved ids`() {
        assertEquals(0, EMPTY_NODE)
        assertEquals(0, ELEM_CELL)
        assertEquals(0, ETREE)
        assertEquals(1, EVAL)
        assertEquals(OriginKey.ReachedStatics, origins.key(OriginTable.REACHED_STATICS))
        assertEquals(OriginKey.ReachedAll, origins.key(OriginTable.REACHED_ALL))
        assertTrue(origins.isMarker(OriginTable.REACHED_STATICS))
        assertTrue(origins.isMarker(OriginTable.REACHED_ALL))
        assertNotEquals(OriginTable.REACHED_STATICS, origins.root(bases.thisBase()))
        assertNotEquals(OriginTable.REACHED_ALL, origins.root(bases.thisBase()))
        assertNotEquals(ETREE, tables.vars.local(0))
        assertNotEquals(EVAL, tables.vars.local(0))
    }

    @Test
    fun `heap key keeps the origin and the cell`() {
        val k = heapKey(123456, 789)
        assertEquals(123456, heapKeyOrigin(k))
        assertEquals(789, heapKeyCell(k))
        assertEquals(ELEM_CELL, heapKeyCell(heapKey(5, ELEM_CELL)))
    }

    @Test
    fun `default content of a sym origin below K is its child`() {
        val x = origins.root(bases.arg(0))
        val xf = origins.child(x, f)
        assertEquals(OriginKey.Sym(bases.arg(0), x, f), origins.key(xf))
        assertEquals(listOf(origins.key(xf)), defaultKeys(x, f))
        assertEquals(1, origins.depth(xf))
        assertEquals(x, origins.parent(xf))
        assertEquals(f, origins.cell(xf))
        assertEquals(bases.arg(0), origins.base(xf))
    }

    @Test
    fun `K boundary gives deep`() {
        val x = origins.root(bases.arg(0))
        val xf = origins.child(x, f)
        val xfg = origins.child(xf, g)
        assertEquals(2, origins.depth(xfg))
        assertEquals(listOf<OriginKey>(OriginKey.Deep(bases.arg(0))), defaultKeys(xfg, f))
        val deep = origins.deep(bases.arg(0))
        assertEquals(deep, origins.child(xfg, f))
        assertEquals(listOf<OriginKey>(OriginKey.Deep(bases.arg(0))), defaultKeys(deep, g))
        assertEquals(deep, origins.child(deep, ELEM_CELL))
    }

    @Test
    fun `default content of both allocation origins is the allocation child`() {
        val s = tables.sites.site(5)
        val n = origins.allocNew(s)
        val o = origins.allocOld(s)
        assertNotEquals(n, o)
        val child = OriginKey.Sym(bases.allocChild(s, f), NO_ID, NO_ID)
        assertEquals(listOf<OriginKey>(child), defaultKeys(n, f))
        assertEquals(origins.defaultNode(n, f), origins.defaultNode(o, f))
        assertNotEquals(origins.defaultNode(n, f), origins.defaultNode(n, g))
        assertEquals(BaseKind.ALLOC_CHILD, bases.kind(bases.allocChild(s, f)))
    }

    @Test
    fun `null const and box bases have own default children`() {
        val s = tables.sites.site(1)
        for (b in listOf(bases.nullAt(s), bases.const("java.lang.String", "abc"), bases.box(s))) {
            val r = origins.root(b)
            assertEquals(listOf<OriginKey>(OriginKey.Sym(b, r, f)), defaultKeys(r, f))
        }
    }

    @Test
    fun `default node is cached for each heap key`() {
        val x = origins.root(bases.arg(0))
        val d1 = origins.defaultNode(x, f)
        val count = origins.size
        val nodeCount = nodes.nodeCount
        assertEquals(d1, origins.defaultNode(x, f))
        assertEquals(count, origins.size)
        assertEquals(nodeCount, nodes.nodeCount)
    }

    @Test
    fun `uniqueness by kind`() {
        val plain = tables.sites.site(1)
        val loop = tables.sites.site(2)
        tables.sites.markLoopSite(loop)

        val thisO = origins.root(bases.thisBase())
        val arg = origins.root(bases.arg(0))
        val stat = origins.root(bases.static("C"))
        val fresh = origins.root(bases.fresh(plain))
        val freshLoop = origins.root(bases.fresh(loop))

        assertTrue(origins.uniqueByKind(thisO))
        assertTrue(origins.uniqueByKind(arg))
        assertTrue(origins.uniqueByKind(origins.child(arg, f)))
        assertTrue(origins.uniqueByKind(origins.child(stat, f)))
        assertTrue(origins.uniqueByKind(fresh))
        assertTrue(origins.uniqueByKind(origins.child(fresh, f)))
        assertTrue(origins.uniqueByKind(origins.allocNew(loop)))
        assertTrue(origins.uniqueByKind(origins.allocNew(plain)))

        // A path with an array cell is not unique.
        assertFalse(origins.uniqueByKind(origins.child(arg, ELEM_CELL)))
        assertFalse(origins.uniqueByKind(origins.child(origins.child(arg, ELEM_CELL), f)))
        assertFalse(origins.uniqueByKind(origins.child(fresh, ELEM_CELL)))
        // A fresh origin of a loop site is not unique.
        assertFalse(origins.uniqueByKind(freshLoop))
        assertFalse(origins.uniqueByKind(origins.child(freshLoop, f)))
        // Never unique.
        assertFalse(origins.uniqueByKind(origins.allocOld(plain)))
        assertFalse(origins.uniqueByKind(origins.deep(bases.arg(0))))
        assertFalse(origins.uniqueByKind(origins.root(bases.allocChild(plain, f))))
        assertFalse(origins.uniqueByKind(origins.root(bases.nullAt(plain))))
        assertFalse(origins.uniqueByKind(origins.root(bases.const("java.lang.Integer", "1"))))
        assertFalse(origins.uniqueByKind(origins.root(bases.box(plain))))
        assertFalse(origins.uniqueByKind(OriginTable.REACHED_STATICS))
        assertFalse(origins.uniqueByKind(OriginTable.REACHED_ALL))
    }

    @Test
    fun `proper ancestors walk the parent chain`() {
        val x = origins.root(bases.arg(0))
        val xf = origins.child(x, f)
        val xfg = origins.child(xf, g)
        val seen = mutableListOf<OriginId>()
        origins.forEachProperAncestor(xfg) { seen += it }
        assertEquals(listOf(xf, x), seen)
        assertTrue(origins.isProperAncestor(x, xfg))
        assertFalse(origins.isProperAncestor(xfg, xfg))
        val none = mutableListOf<OriginId>()
        origins.forEachProperAncestor(x) { none += it }
        origins.forEachProperAncestor(origins.allocNew(tables.sites.site(0))) { none += it }
        assertEquals(emptyList(), none)
    }

    @Test
    fun `bases are interned by key`() {
        val s0 = tables.sites.site(0)
        val s1 = tables.sites.site(1)
        assertEquals(bases.static("a.C"), bases.static("a.C", "a.C<T>"))
        assertEquals("a.C<T>", bases.staticTypeName(bases.static("a.C")))
        // The first recorded type name stays.
        bases.static("a.C", "other")
        assertEquals("a.C<T>", bases.staticTypeName(bases.static("a.C")))
        assertEquals(bases.const("java.lang.String", "x"), bases.const("java.lang.String", "x"))
        assertNotEquals(bases.const("java.lang.String", "1"), bases.const("java.lang.Integer", "1"))
        assertNotEquals(bases.nullAt(s0), bases.nullAt(s1))
        assertNotEquals(bases.box(s0), bases.box(s1))
        assertNotEquals(bases.fresh(s0), bases.box(s0))
        assertEquals(BaseKey.Arg(3), bases.key(bases.arg(3)))
        assertEquals(BaseKind.STATIC, bases.kind(bases.static("a.C")))
    }

    @Test
    fun `tables give stable ids`() {
        assertEquals(tables.vars.local(3), tables.vars.local(3, ROOT_CONTEXT))
        assertNotEquals(tables.vars.local(3), tables.vars.local(3, 1))
        assertEquals(VarTable.LocalKey(3, 1), tables.vars.key(tables.vars.local(3, 1)))
        assertEquals(tables.sites.site(4), tables.sites.site(4, ROOT_CONTEXT))
        assertEquals(SiteTable.SiteKey(4, ROOT_CONTEXT), tables.sites.key(tables.sites.site(4)))
        assertEquals(f, tables.cells.field("C", "f", "java.lang.Object"))
        assertEquals(CellTable.FieldKey("C", "f", "java.lang.Object"), tables.cells.fieldKey(f))
        assertNotEquals(ELEM_CELL, f)
    }

    @Test
    fun `frozen tables refuse new ids`() {
        val x = origins.root(bases.arg(0))
        val dx = origins.defaultNode(x, f)
        tables.freeze()
        assertEquals(dx, origins.defaultNode(x, f))
        assertEquals(NO_ID, origins.findChild(x, g))
        assertFailsWith<IllegalStateException> { origins.child(x, g) }
        assertFailsWith<IllegalStateException> { tables.vars.local(99) }
        assertFailsWith<IllegalStateException> { tables.cells.field("D", "h", "int") }
        assertContentEquals(intArrayOf(origins.child(x, f)), nodes.members(dx))
    }

    @Test
    fun `a frozen base table refuses a new static type name`() {
        val named = bases.static("C", "C")
        val unnamed = bases.static("D")
        tables.freeze()
        // A lookup works. The recorded name stays.
        assertEquals(named, bases.static("C", "C"))
        assertEquals(named, bases.static("C", "Other"))
        assertEquals("C", bases.staticTypeName(named))
        assertEquals(unnamed, bases.static("D"))
        // A new name is a write: the frozen table refuses it.
        assertFailsWith<IllegalStateException> { bases.static("D", "D") }
        assertEquals(null, bases.staticTypeName(unnamed))
    }
}
