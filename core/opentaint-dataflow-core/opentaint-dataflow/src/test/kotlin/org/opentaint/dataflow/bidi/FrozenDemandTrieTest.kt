package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.fixtures.TestMark
import org.opentaint.dataflow.bidi.fixtures.testDeclarations
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

class FrozenDemandTrieTest {
    @Test
    fun `C2 and C5 retain their distinct FULL group and exclusion relations`() {
        val f = StoreFixtures(markDeclarations = testDeclarations(
            TestMark("T", MarkGroupKey.Rule("r")), TestMark("U", MarkGroupKey.Rule("r")),
            TestMark("V", MarkGroupKey.Rule("s"))))
        val t = f.mark("T"); val u = f.mark("U"); val v = f.mark("V")
        val group = f.manager.marks.group(f.manager.marks.groupOf(t))
        val marks = listOf(MarkSlot.STAR, MarkSlot.Star(f.manager.markSetOf(t)),
            MarkSlot.Concrete(t), MarkSlot.Concrete(u), MarkSlot.Concrete(v), MarkSlot.Concrete(group))
        val patterns = marks.map { f.pattern(tail = Tail.ANY, mark = it) }
        val trie = FrozenDemandTrie.Builder<Int>().apply { patterns.forEachIndexed { id, p -> add(p, id) } }.build()
        for (actual in patterns) for (kind in DemandQueryKind.entries) {
            val expected = patterns.indices.filter { id ->
                if (kind == DemandQueryKind.INITIAL_C2) markSub(patterns[id].fact.mark, actual.fact.mark, f.manager.marks)
                else marksMeet(patterns[id].fact.mark, actual.fact.mark, f.manager.marks)
            }
            val selected = ArrayList<Int>()
            trie.visitNativeOrder(actual, kind, f.manager.marks, selected::add)
            assertEquals(expected, selected, "$kind $actual")
        }
    }

    @Test
    fun `DATA control entry is present in the precision trie and C2`() {
        val f = StoreFixtures()
        val pattern = f.pattern(path = listOf(f.field("f")), tail = Tail.ANY)
        val scope = BlockScope(org.opentaint.dataflow.graph.BlockId(2), org.opentaint.dataflow.graph.PortId(5))
        val store = DemandStore.Builder(f.manager).apply {
            add(f.method, scope, org.opentaint.dataflow.graph.PortId(6), PairedDemand(DemandEntry.Data(pattern), DemandExit.Zero))
        }.build()
        val view = store.scope(f.method, scope)
        val actual = f.fact(path = pattern.fact.path + f.field("g"), mark = pattern.fact.mark)
        val policy = RestrictedInitialPolicy(3, 8, Direction.FORWARD, f.manager.marks)
        assertTrue(view.initials(actual, policy).isNotEmpty())
        val cursor = assertNotNull((view as EntryPrecisionView).precisionCursors(f.ops.leaves(actual).single(), policy)).single()
        assertEquals(pattern, cursor.subtreeWitness())
    }

    @Test
    fun `profile selection preserves native prefix and subtree order`() {
        val f = StoreFixtures()
        val base = AccessPathBase.Argument(0)
        val marks = listOf(MarkSlot.STAR, MarkSlot.Concrete(f.mark("T")), MarkSlot.Concrete(f.mark("U")))
        val paths = listOf(emptyList<Int>()) + (0 until 32).map { listOf(f.field("f$it")) } +
            (0 until 12).map { listOf(f.field("f${it % 4}"), f.field("g$it")) }
        val patterns = paths.flatMap { path -> marks.map { f.pattern(base, path, Tail.ANY, it) } }
        val reference = PathTrie<Int>()
        val builder = FrozenDemandTrie.Builder<Int>(f.cancellation)
        patterns.forEachIndexed { id, pattern ->
            reference.add(base, pattern.fact.path.toIntArray(), id)
            assertTrue(builder.add(pattern, id))
            assertFalse(builder.add(pattern, id))
        }
        val trie = builder.build()
        for (path in paths + listOf(listOf(f.field("absent")))) for (mark in marks) {
            val actual = f.pattern(base, path, Tail.EXACT, mark)
            for (kind in DemandQueryKind.entries) {
                fun eligible(id: Int) = if (kind == DemandQueryKind.INITIAL_C2)
                    markSub(patterns[id].fact.mark, mark, f.manager.marks)
                else marksMeet(patterns[id].fact.mark, mark, f.manager.marks)
                val expected = reference.around(base, path.toIntArray()).filter(::eligible)
                val selected = ArrayList<Int>()
                trie.visitNativeOrder(actual, kind, f.manager.marks, selected::add)
                assertEquals(expected, selected, "$kind $actual")
            }
        }
    }

    @Test
    fun `precision cursors use compatible ANY witnesses without descendant enumeration`() {
        val f = StoreFixtures()
        val x = AccessPathBase.Argument(0)
        val a = f.field("f"); val b = f.field("g"); val c = f.field("h")
        val t = MarkSlot.Concrete(f.mark("T")); val u = MarkSlot.Concrete(f.mark("U"))
        val builder = FrozenDemandTrie.Builder<Pattern>(f.cancellation)
        val short = f.pattern(x, listOf(a), Tail.ANY, t)
        val long = f.pattern(x, listOf(a, b), Tail.ANY, t)
        val wrongMark = f.pattern(x, listOf(a, b, c), Tail.ANY, u)
        val exact = f.pattern(x, listOf(a, b, c), Tail.EXACT, t)
        listOf(short, long, wrongMark, exact).forEach { builder.add(it, it) }
        val trie = builder.build()
        val cursor = trie.precisionCursors(f.pattern(x, listOf(a, b, c), mark = t), f.manager.marks).single()
        assertEquals(short, cursor.subtreeWitness())
        val atF = assertNotNull(cursor.follow(a))
        assertEquals(short, atF.subtreeWitness())
        val atG = assertNotNull(atF.follow(b))
        assertEquals(long, atG.subtreeWitness())
        assertNull(atG.follow(c), "An exact-only child cannot extend an ANY precision cursor")
        assertFalse(trie.hasBase(AccessPathBase.Return))
    }
}
