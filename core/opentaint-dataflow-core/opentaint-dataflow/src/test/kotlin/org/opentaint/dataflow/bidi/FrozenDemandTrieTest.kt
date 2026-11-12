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
                val expected = reference.around(base, path.toIntArray()).filter { eligible(it) &&
                    (kind != DemandQueryKind.INITIAL_C2 || patterns[it].fact.path.size <= path.size) }
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
    @Test fun `C2 skips impossible strict descendants while C5 retains them`() {
        val f = StoreFixtures()
        val root = f.pattern(tail = Tail.ANY)
        val child = f.pattern(path = listOf(f.field("f")), tail = Tail.ANY)
        val trie = FrozenDemandTrie.Builder<Int>().apply { add(root, 0); add(child, 1) }.build()
        for (tail in Tail.entries) for (kind in DemandQueryKind.entries) {
            val selected = arrayListOf<Int>()
            var nodes = -1L
            trie.visitCountedNativeOrder(root.copy(fact = root.fact.copy(tail = tail)), kind,
                f.manager.marks, { n, _, _ -> nodes = n }, selected::add)
            val descend = kind != DemandQueryKind.INITIAL_C2 || tail.isAny
            assertEquals(if (descend) listOf(0, 1) else listOf(0), selected)
            assertEquals(if (descend) 2L else 1L, nodes)
        }
    }

    @Test fun `STOP unwinds ancestors and descendants and finalizes counts`() {
        val f = StoreFixtures()
        val root = f.pattern(tail = Tail.ANY)
        val child = f.pattern(path = listOf(f.field("f")), tail = Tail.ANY)
        val trie = FrozenDemandTrie.Builder<Int>().apply { add(root, 0); add(child, 1) }.build()
        for (actual in listOf(root, child)) {
            val selected = arrayListOf<Int>()
            var counts = emptyList<Long>()
            val status = trie.visitCountedUntil(actual, DemandQueryKind.INITIAL_C2, f.manager.marks,
                { n, p, c -> counts = listOf(n, p, c) }) {
                selected += it
                DemandVisit.STOP
            }
            assertEquals(DemandScan.STOPPED, status)
            assertEquals(listOf(0), selected)
            assertEquals(listOf(1L, 1L, 1L), counts)
        }
    }

    @Test fun `pure local scan matches complete materialized families and stops on companions`() {
        val f = StoreFixtures()
        val scope = BlockScope(org.opentaint.dataflow.graph.BlockId(1), org.opentaint.dataflow.graph.PortId(2))
        val d = f.pattern(tail = Tail.ANY)
        val store = DemandStore.Builder(f.manager).apply {
            add(f.method, scope, org.opentaint.dataflow.graph.PortId(3), DemandPattern(d, d))
        }.build()
        val view = store.scope(f.method, scope)
        val scan = view as LocalAdmissionView
        val policy = RestrictedInitialPolicy(3, 8, Direction.FORWARD, f.manager.marks)
        for (tail in Tail.entries) for (layer in Layer.entries) {
            val actual = f.fact(path = listOf(f.field("f")), tail = tail, layer = layer)
            val emitted = arrayListOf<InitialEmission>()
            assertEquals(DemandScan.COMPLETED, scan.visitInitialEmissions(actual, policy) {
                emitted += it; DemandVisit.CONTINUE
            })
            assertEquals(view.initials(actual, policy).map { InitialEmission(it.initial.toPattern(), it.layer) }, emitted)
        }
        val actual = f.fact(path = listOf(f.field("f"), f.field("g")))
        var visited = 0
        assertEquals(DemandScan.STOPPED, scan.visitInitialEmissions(actual, policy) {
            visited++; if (visited == 2) DemandVisit.STOP else DemandVisit.CONTINUE
        })
        assertEquals(2, visited)
        val later = RestrictedInitialPolicy(2, 8, Direction.BACKWARD, f.manager.marks)
        assertFalse(scan.supportsScan(actual, later))
        assertEquals(DemandScan.UNSUPPORTED, scan.visitInitialEmissions(actual, later) { error("unsupported scan") })
        assertEquals(DemandScan.UNSUPPORTED, scan.visitInitialEmissions(Reach.NORMAL, policy) { error("control scan") })
    }

    @Test fun `visitor exception and cancellation unwind with final work counts`() {
        val f = StoreFixtures()
        val root = f.pattern(tail = Tail.ANY)
        val trie = FrozenDemandTrie.Builder<Int>(f.cancellation).apply { add(root, 0); add(root, 1) }.build()
        var counts = emptyList<Long>()
        assertFailsWith<IllegalStateException> {
            trie.visitCountedUntil(root, DemandQueryKind.INITIAL_C2, f.manager.marks,
                { n, p, c -> counts = listOf(n, p, c) }) { error("visitor error") }
        }
        assertEquals(listOf(1L, 1L, 1L), counts)
        assertFailsWith<org.opentaint.dataflow.util.Cancellation.Cancelled> {
            trie.visitCountedUntil(root, DemandQueryKind.INITIAL_C2, f.manager.marks,
                { n, p, c -> counts = listOf(n, p, c) }) {
                f.cancellation.cancel()
                DemandVisit.CONTINUE
            }
        }
        assertEquals(listOf(1L, 1L, 1L), counts)
    }

    @Test fun `pure emission scan does not intern primary or companion initials`() {
        val f = StoreFixtures()
        val scope = BlockScope(org.opentaint.dataflow.graph.BlockId(1), org.opentaint.dataflow.graph.PortId(2))
        val d = f.pattern(tail = Tail.ANY)
        val view = DemandStore.Builder(f.manager).apply {
            add(f.method, scope, org.opentaint.dataflow.graph.PortId(3), DemandPattern(d, d))
        }.build().scope(f.method, scope) as LocalAdmissionView
        val actual = f.fact(path = listOf(f.field("f"), f.field("g")))
        val directory = ApManager::class.java.getDeclaredField("initials").apply { isAccessible = true }
        fun count() = (directory.get(f.manager) as Map<*, *>).size
        val before = count()
        val emitted = arrayListOf<InitialEmission>()
        assertEquals(DemandScan.COMPLETED, view.visitInitialEmissions(actual,
            RestrictedInitialPolicy(3, 8, Direction.FORWARD, f.manager.marks)) {
            emitted += it; DemandVisit.CONTINUE
        })
        assertEquals(3, emitted.size)
        assertEquals(before, count(), "The descriptor probe must not create query-only initial keys")
    }

}
