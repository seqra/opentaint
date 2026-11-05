package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class NormalStarRelationStoreTest {
    private val f = StoreFixtures()
    private val ap = f.manager
    private val x = AccessPathBase.Argument(0)
    private val y = AccessPathBase.Return
    private val a = f.field("a")
    private val b = f.field("b")
    private val c = f.field("c")
    private fun initial(path: List<Int> = emptyList(), e: ExclusionSet = ExclusionSet.Empty) =
        ap.initial(f.pattern(x, path, Tail.STAR, MarkSlot.STAR, e))
    private fun flow(path: List<Int> = emptyList(), e: ExclusionSet = ExclusionSet.Empty,
                     mx: MarkSet = MarkSet.EMPTY) =
        ap.flowTree(y, Layer.NORMAL, e, mx,
            FlowAlgebra.prepend(ap, ap.path(path), FlowAlgebra.LEAF_NODE), Tail.STAR)
    private fun paths(store: RunSummaryStore) = store.all().map { (i, value) ->
        (i as InitialAp).toPattern().fact.path to f.ops.leaves(value).map { it.fact.path }.toList()
    }.toSet()

    @Test fun `both summary backends keep the actual shortest aligned pair in either order`() {
        for (backed in listOf(false, true)) for (shortFirst in listOf(false, true)) {
            val store = RunSummaryStore(ap, flowBacked = backed)
            val short = initial() to flow()
            val long = initial(listOf(a)) to flow(listOf(a))
            for ((i, value) in if (shortFirst) listOf(short, long) else listOf(long, short))
                store.addAdmitted(i, value)
            assertEquals(setOf(emptyList<Int>() to listOf(emptyList<Int>())), paths(store))
            assertTrue(store.borrow(long.first).none())
            assertNull(store.addAdmitted(long.first, long.second))
        }
    }

    @Test fun `same input keeps independent output bases through native header canonicalization`() {
        val bases = listOf(x, y, AccessPathBase.LocalVar(7))
        fun output(base: AccessPathBase, path: List<Int>) = ap.flowTree(base, Layer.NORMAL,
            ExclusionSet.Empty, MarkSet.EMPTY,
            FlowAlgebra.prepend(ap, ap.path(path), FlowAlgebra.LEAF_NODE), Tail.STAR)
        val short = bases.map { initial() to output(it, emptyList()) }
        val long = bases.map { initial(listOf(a)) to output(it, listOf(a)) }
        val expected = short.toSet()
        for (backed in listOf(false, true)) for (shortFirst in listOf(false, true)) {
            val rows = if (shortFirst) short + long.reversed() else long + short.reversed()
            val store = RunSummaryStore(ap, flowBacked = backed)
            val publications = PublicationIndex(ap, f.ops, flowBacked = backed)
            for ((i, value) in rows) store.addAdmittedAll(i, value)
            publications.addAll(rows.map { Publication(it.first, it.second) })
            assertEquals(expected, store.all().map { it.first to it.second }.toSet())
            assertEquals(expected, publications.currentPublications().map { it.premise to it.conclusion }.toSet())
            assertTrue(store.borrow(initial(listOf(a))).none())
            for (direction in Direction.entries) {
                val records = PersistentRecordStore(ap)
                for ((i, value) in rows) records.add(Record(f.method, direction, i, value))
                val current = records.byEntry(f.method, initial().toPattern()).toList()
                assertEquals(expected, current.map { it.premise to it.conclusion }.toSet())
                for (base in bases) {
                    val reverse = records.byExit(f.method,
                        f.pattern(base, tail = Tail.STAR, mark = MarkSlot.STAR)).toList()
                    assertEquals(1, reverse.size)
                    assertEquals(base, reverse.single().conclusion.base)
                    assertSame(initial(), reverse.single().premise)
                }
            }
        }
    }

    @Test fun `packed longer siblings do not invent a missing root and lose only covered leaves`() {
        val store = RunSummaryStore(ap, flowBacked = true)
        store.addAdmitted(initial(listOf(a)), flow(listOf(a)))
        store.addAdmitted(initial(listOf(b)), flow(listOf(b)))
        assertEquals(2, store.all().count())
        assertTrue(store.borrow(initial()).none())
        val mixed = ap.mergeAddDelta(flow(listOf(a)), flow(listOf(c))).first
        store.addAdmitted(initial(), mixed)
        assertEquals(setOf(emptyList<Int>() to listOf(listOf(a), listOf(c)),
            listOf(a) to listOf(listOf(a)), listOf(b) to listOf(listOf(b))), paths(store))
        // A genuine root pair covers both aligned longer inputs, not the extra q.a/q.c outputs.
        store.addAdmitted(initial(), flow())
        assertEquals(setOf(emptyList<Int>() to listOf(emptyList<Int>(), listOf(a), listOf(c))), paths(store))
    }

    @Test fun `unaligned geometry exclusions and incompatible mark headers remain separate`() {
        val store = RunSummaryStore(ap, flowBacked = true)
        store.addAdmitted(initial(), flow(mx = ap.markSetOf(f.mark("T"))))
        store.addAdmitted(initial(listOf(a)), flow(listOf(b)))
        store.addAdmitted(initial(listOf(b), ExclusionSet.of(intArrayOf(c))), flow(listOf(b)))
        store.addAdmitted(initial(listOf(c)), flow(listOf(c)))
        assertEquals(4, store.all().count())
    }

    @Test fun `publication batch and later replay have only canonical current pairs`() {
        for (backed in listOf(false, true)) {
            val index = PublicationIndex(ap, f.ops, flowBacked = backed)
            val long = Publication(initial(listOf(a)), flow(listOf(a)))
            val short = Publication(initial(), flow())
            val fresh = index.addAll(listOf(long, short))
            assertEquals(listOf(short), fresh)
            val current = index.candidates(initial(), f.fact(x, listOf(a, b), Tail.STAR, MarkSlot.STAR),
                ApMode(false, Direction.FORWARD, 4))
            assertEquals(listOf(short), current.map { it.first })
            assertTrue(index.addAll(listOf(long)).isEmpty())
        }
    }

    @Test fun `specialized FLOW cover still removes marked STAR after longer FLOW disappears`() {
        val store = RunSummaryStore(ap, flowBacked = true)
        store.addAdmitted(initial(listOf(a)), flow(listOf(a)))
        store.addAdmitted(initial(), flow())
        val markedI = ap.initial(f.pattern(x, listOf(a), Tail.STAR))
        val marked = f.fact(y, listOf(a), Tail.STAR, layer = Layer.DEMAND) as TaintTree
        assertNull(store.addAdmitted(markedI, marked))
        val protected = marked.withProtection(marked.root)
        assertNotNull(store.addAdmitted(markedI, protected))
        assertTrue(store.borrow(markedI).filterIsInstance<TaintTree>().all { it.nonSubsumable != null })
    }

    @Test fun `persistent direct and reverse indexes discard obsolete longer records`() {
        for (direction in Direction.entries) {
            val records = PersistentRecordStore(ap)
            val scope = BlockScope(BlockId(2), PortId(3))
            val exit = PortId(4)
            records.add(Record(f.method, direction, initial(listOf(a)), flow(listOf(a)), scope, exit))
            records.add(Record(f.method, direction, initial(), flow(), scope, exit))
            val direct = records.byEntry(f.method, scope, f.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR)).toList()
            assertEquals(1, direct.size)
            assertSame(initial(), direct.single().premise)
            val reverse = records.byExitPositions(f.method, BlockScope(scope.block, exit),
                f.pattern(y, tail = Tail.STAR, mark = MarkSlot.STAR))
            assertEquals(1, reverse.size)
            assertEquals(emptyList(), reverse.single().path)
            assertSame(direct.single(), reverse.single().record)
            assertTrue(records.byEntry(f.method, BlockScope(scope.block, PortId(7)), f.pattern(x)).none())
        }
    }

    @Test fun `aligned packed families retain DAG sharing without enumerating concrete paths`() {
        var root = FlowAlgebra.LEAF_NODE
        repeat(24) { root = FlowAlgebra.node(FlowLeaf.NONE, intArrayOf(a, b), arrayOf(root, root)) }
        val short = ap.flowTree(y, Layer.NORMAL, ExclusionSet.Empty, MarkSet.EMPTY, root, Tail.STAR)
        val suffix = FlowAlgebra.prepend(ap, ap.path(listOf(c)), FlowAlgebra.LEAF_NODE)
        val longRoot = assertNotNull(FlowAlgebra.graft(root, { it == FlowLeaf.LEAF }, suffix, ap.cancellation))
        val long = short.withRoot(longRoot)
        val store = RunSummaryStore(ap, flowBacked = true)
        assertNotNull(store.addAdmitted(initial(), short))
        assertNull(store.addAdmitted(initial(listOf(c)), long))
        val kept = store.all().single().second as FlowTree
        assertSame(kept.root.children!![0], kept.root.children!![1])
        assertEquals(root.boundedDepth, kept.root.boundedDepth)
    }

    @Test fun `detached spatial MAY and MUST batches omit coordinates removed by a later broad row`() {
        for (backed in listOf(false, true)) for (tail in listOf(Tail.ANY, Tail.ANY_TAINT)) {
            val index = PublicationIndex(ap, f.ops, flowBacked = backed)
            val layer = if (tail == Tail.ANY) Layer.DEMAND else Layer.NORMAL
            fun value(path: List<Int>) = ap.flowTree(y, layer, ExclusionSet.Empty, MarkSet.EMPTY,
                FlowAlgebra.prepend(ap, ap.path(path), FlowAlgebra.LEAF_NODE), tail)
            val broad = value(emptyList())
            val fresh = index.addAll(listOf(Publication(initial(), value(listOf(a))), Publication(initial(), broad)))
            assertEquals(listOf(Publication(initial(), broad)), fresh, "backed=$backed tail=$tail")
        }
    }

    @Test fun `detached E refill retains protected exact slots across current wrapper cohorts`() {
        for (backed in listOf(false, true)) {
            val index = PublicationIndex(ap, f.ops, flowBacked = backed)
            val key = ap.initial(f.pattern(x))
            val exact = f.fact(y, listOf(b)) as TaintTree
            val parent = f.fact(y, tail = Tail.ANY_TAINT, exclusion = ExclusionSet.of(a)) as TaintTree
            val mixed = ap.taintTree(y, Layer.NORMAL,
                ap.taintAlg.mergeAdd(parent.root, exact.root), parent.exclusion, Tail.ANY_TAINT, exact.root)
            val fill = f.fact(y, listOf(a), Tail.ANY_TAINT)
            val fresh = index.addAll(listOf(Publication(key, mixed), Publication(key, fill)))
            val members = fresh.flatMap { pub -> f.ops.leaves(pub.conclusion).map {
                Conclusion(it.fact, it.exclusion, pub.conclusion.layer == Layer.DEMAND)
            }.toList() }.toSet()
            assertTrue(members.any { it.fact.path.isEmpty() && it.fact.tail == Tail.ANY_TAINT && it.exclusion == ExclusionSet.Empty })
            assertTrue(members.any { it.fact.path == listOf(b) && it.fact.tail == Tail.EXACT })
            assertFalse(members.any { it.fact.path == listOf(a) && it.fact.tail == Tail.ANY_TAINT })
            assertFalse(members.any { it.fact.tail == Tail.ANY_TAINT && it.exclusion != ExclusionSet.Empty })
            assertTrue(fresh.any { (it.conclusion as? TaintTree)?.nonSubsumable != null })
        }
    }

    @Test fun `completed persistence batches remain read only through a view`() {
        val records = PersistentRecordStore(ap)
        val current = RunSummaryStore(ap)
        current.addAdmitted(initial(listOf(a)), flow(listOf(a)))
        records.add(Record(f.method, Direction.FORWARD, initial(), flow()))
        records.persistCompleted(Direction.FORWARD, sequenceOf(f.method to current), emptySequence())
        assertEquals(1, records.byEntry(f.method, f.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR)).count())
        assertFailsWith<IllegalStateException> {
            records.view().persistCompleted(Direction.FORWARD, emptySequence(), emptySequence())
        }
    }

    @Test fun `equal nonempty full mark exclusions cover without mixing different masks`() {
        val store = RunSummaryStore(ap, flowBacked = true)
        val excludedT = ap.markSetOf(f.mark("T"))
        store.addAdmitted(initial(), flow(mx = excludedT))
        assertNull(store.addAdmitted(initial(listOf(a)), flow(listOf(a), mx = excludedT)))
        assertNotNull(store.addAdmitted(initial(listOf(a)), flow(listOf(a), mx = ap.markSetOf(f.mark("U")))))
        assertEquals(2, store.all().count())
    }

    @Test fun `point backend does not enable cross premise relation canonicalization`() {
        val point = FlowBackedSummaries(ap, replaceCovered = false)
        point.addAll(initial(), flow())
        point.addAll(initial(listOf(a)), flow(listOf(a)))
        assertEquals(2, point.all().count())
        assertEquals(1, point.borrow(initial(listOf(a))).count())
    }

    @Test fun `implicit FLOW specialization removes marked relation in every ABC order on both backends`() {
        val permutations = listOf(listOf(0, 1, 2), listOf(0, 2, 1), listOf(1, 0, 2),
            listOf(1, 2, 0), listOf(2, 0, 1), listOf(2, 1, 0))
        for (backed in listOf(false, true)) for (variant in 0..2) for (order in permutations) {
            val mx = if (variant == 2) ap.markSetOf(f.mark("T")) else MarkSet.EMPTY
            val root = Publication(initial(), flow(mx = mx))
            val specialized = Publication(initial(listOf(a)), flow(listOf(a), mx = mx))
            val markedI = ap.initial(f.pattern(x, listOf(a), Tail.STAR))
            val plain = f.fact(y, listOf(a), Tail.STAR) as TaintTree
            val marked = Publication(markedI, if (variant == 1) plain.withProtection(plain.root) else plain)
            val offered = listOf(root, specialized, marked)
            val store = RunSummaryStore(ap, flowBacked = backed)
            val index = PublicationIndex(ap, f.ops, flowBacked = backed)
            for (item in order.map(offered::get)) {
                store.addAdmittedAll(item.premise, item.conclusion)
                index.addAll(listOf(item))
            }
            val expected = if (variant == 0) setOf(root) else setOf(root, marked)
            val label = "backed=$backed variant=$variant order=$order"
            assertEquals(expected, store.all().map { Publication(it.first, it.second) }.toSet(), label)
            assertEquals(expected, index.currentPublications().toSet(), label)
            if (variant == 1) assertTrue(store.borrow(markedI).filterIsInstance<TaintTree>()
                .all { it.nonSubsumable != null }, label)
            // A single detached batch must suppress C/B portions obsolete by its end too.
            val batch = PublicationIndex(ap, f.ops, flowBacked = backed)
            assertEquals(expected, batch.addAll(order.map(offered::get)).toSet(), label)
        }
        // C-first followed by A alone: no B ever had to be admitted.
        for (backed in listOf(false, true)) {
            val store = RunSummaryStore(ap, flowBacked = backed)
            store.addAdmittedAll(ap.initial(f.pattern(x, listOf(a), Tail.STAR)), f.fact(y, listOf(a), Tail.STAR))
            store.addAdmittedAll(initial(), flow())
            assertEquals(listOf(initial() to flow()), store.all().toList())
        }
    }

    @Test fun `packed admission agrees with scalar aligned cover after every batch`() {
        data class Row(val input: List<Int>, val output: List<Int>)
        fun covers(short: Row, long: Row): Boolean = long.input.size >= short.input.size &&
            long.input.take(short.input.size) == short.input &&
            short.output + long.input.drop(short.input.size) == long.output
        val paths = listOf(emptyList(), listOf(a), listOf(b), listOf(a, a), listOf(a, b), listOf(b, a))
        for (backed in listOf(false, true)) for (seed in 0..3) {
            val random = kotlin.random.Random(seed)
            val store = RunSummaryStore(ap, flowBacked = backed)
            var reference = emptyList<Row>()
            repeat(40) {
                val input = paths[random.nextInt(paths.size)]
                val outputs = List(3) { paths[random.nextInt(paths.size)] }.distinct()
                var root: FlowNode? = null
                for (output in outputs) {
                    val one = flow(output).root
                    root = root?.let { FlowAlgebra.mergeAdd(it, one) } ?: one
                    val row = Row(input, output)
                    if (reference.none { covers(it, row) }) reference = reference.filterNot { covers(row, it) } + row
                }
                store.addAdmittedAll(initial(input), flow().withRoot(assertNotNull(root)))
                val actual = store.all().flatMap { (i, value) -> f.ops.leaves(value).map {
                    Row((i as InitialAp).toPattern().fact.path, it.fact.path)
                } }.toSet()
                assertEquals(reference.toSet(), actual, "backed=$backed seed=$seed")
            }
        }
    }

    @Test fun `native mx coverage composes with aligned geometry without a retained intermediate`() {
        val permutations = listOf(listOf(0, 1, 2), listOf(0, 2, 1), listOf(1, 0, 2),
            listOf(1, 2, 0), listOf(2, 0, 1), listOf(2, 1, 0))
        val excluded = ap.markSetOf(f.mark("T"))
        val broad = Publication(initial(), flow())
        val intermediate = Publication(initial(), flow(mx = excluded))
        val narrow = Publication(initial(listOf(a)), flow(listOf(a), mx = excluded))
        val rows = listOf(broad, intermediate, narrow)
        for (backed in listOf(false, true)) for (order in permutations) {
            val store = RunSummaryStore(ap, flowBacked = backed)
            val index = PublicationIndex(ap, f.ops, flowBacked = backed)
            for (row in order.map(rows::get)) {
                store.addAdmittedAll(row.premise, row.conclusion)
                index.addAll(listOf(row))
            }
            val label = "backed=$backed order=$order"
            assertEquals(listOf(broad), store.all().map { Publication(it.first, it.second) }.toList(), label)
            assertEquals(listOf(broad), index.currentPublications(), label)
            val batch = PublicationIndex(ap, f.ops, flowBacked = backed)
            assertEquals(setOf(broad), batch.addAll(order.map(rows::get)).toSet(), label)
        }
    }
}
