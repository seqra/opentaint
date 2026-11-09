package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.util.Cancellation
import kotlin.random.Random
import kotlin.test.*

/** Independent finite location oracle for the selected class-separated union laws.
 * The old OR-upgrade oracle is deliberately not used for the new contract. */
class TaintAdmissionProtectionTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val t = fixture.mark("T")
    private val u = fixture.mark("U")
    private val x = AccessPathBase.Argument(0)
    private val empty = ExclusionSet.Empty
    private data class Coordinate(val path: List<Int>, val exact: Boolean, val mark: Int)
    private data class Location(val path: List<Int>, val mark: Int, val layer: Layer, val protected: Boolean)
    private fun c(path: List<Int>, exact: Boolean = true, mark: TaintMark = t) = Coordinate(path, exact, mark.id)
    private fun root(coordinates: Collection<Coordinate>): TaintNode = coordinates.map {
        val marks = MarkSet(intArrayOf(it.mark))
        val leaf = if (it.exact) m.taintLeaves(marks, MarkSet.EMPTY) else m.taintLeaves(MarkSet.EMPTY, marks)
        m.taintAlg.prepend(m, m.path(it.path), m.taintAlg.leafNode(leaf))
    }.reduce { a, b -> m.taintAlg.mergeAdd(a, b, m.cancellation) }
    private fun tree(coordinates: Set<Coordinate>, protected: Set<Coordinate> = emptySet(),
                     tail: Tail = Tail.ANY_TAINT, exclusion: ExclusionSet = empty,
                     layer: Layer = Layer.NORMAL): TaintTree =
        m.taintTree(x, layer, root(coordinates), exclusion, tail,
            protected.takeIf { it.isNotEmpty() }?.let(::root))
    private fun coordinates(root: TaintNode?): Set<Coordinate> = buildSet {
        if (root == null) return@buildSet
        val pending = ArrayDeque<Pair<List<Int>, TaintNode>>()
        pending += emptyList<Int>() to root
        while (pending.isNotEmpty()) {
            val (path, node) = pending.removeLast()
            node.leaf.exact.ids.forEach { add(Coordinate(path, true, it)) }
            node.leaf.any.ids.forEach { add(Coordinate(path, false, it)) }
            node.accessorData?.forEachIndexed { i, field -> pending += path + field to node.childData!![i] }
        }
    }
    private val paths: List<List<Int>> = buildList {
        var level = listOf(emptyList<Int>())
        addAll(level)
        repeat(4) { level = level.flatMap { p -> listOf(p + f, p + g) }; addAll(level) }
    }
    private fun denotation(values: List<TaintTree>): Set<Location> = buildSet {
        for (value in values) {
            val flags = coordinates(value.nonSubsumable)
            val excluded = (value.exclusion as? ExclusionSet.Concrete)?.ids?.toSet().orEmpty()
            for (at in coordinates(value.root)) for (path in paths) {
                if (path.size < at.path.size || path.take(at.path.size) != at.path) continue
                val suffix = path.drop(at.path.size)
                if (at.exact && suffix.isNotEmpty()) continue
                if (!at.exact && value.anyTail != Tail.ANY && suffix.isNotEmpty() && suffix[0] in excluded) continue
                add(Location(path, at.mark, value.layer, at in flags))
            }
        }
    }
    private fun checkSequence(inputs: List<TaintTree>) {
        val actual = TaintGroup(m, m.newInterners().taint)
        val offered = ArrayList<TaintTree>()
        var previous = emptySet<Location>()
        for ((i, input) in inputs.withIndex()) {
            offered += input
            val expected = denotation(offered)
            val delta = actual.addAll(input)
            val current = actual.all().toList()
            assertEquals(expected, denotation(current), "retained union at $i")
            assertTrue(denotation(delta).containsAll(expected - previous), "new semantic support at $i")
            assertTrue(expected.containsAll(denotation(delta)), "delta stays within current union at $i")
            for (packet in current) assertTrue(packet.nonSubsumable == null || packet.nonSubsumable == packet.root)
            assertEquals(current.size, current.map { it.groupKey }.toSet().size, "one packet per class/header")
            previous = expected
        }
    }

    @Test fun `finite typed cells retain both memberships for every ordered pair`() {
        val a = c(listOf(f))
        val b = c(listOf(g), false, u)
        val cells = buildList {
            for (layer in Layer.entries) for (tail in listOf(Tail.STAR, Tail.ANY, Tail.ANY_TAINT))
                for (e in if (tail == Tail.ANY) listOf(empty) else listOf(empty, ExclusionSet.of(f)))
                    for (ordinary in listOf(setOf(a), setOf(b), setOf(a, b)))
                        for (mask in listOf(emptySet(), setOf(ordinary.first()), ordinary))
                            add(tree(ordinary, mask, tail, e, layer))
        }
        for (first in cells) for (second in cells) checkSequence(listOf(first, second, first, second))
    }

    @Test fun `random mixed admissions retain the independent class denotation`() {
        val random = Random(734279)
        val universe = listOf(c(emptyList()), c(listOf(f)), c(listOf(g), mark = u),
            c(emptyList(), false), c(listOf(f), false), c(listOf(g, f), false, u))
        repeat(20) {
            val inputs = List(30) {
                val ordinary = universe.filter { random.nextBoolean() }.toSet().ifEmpty { setOf(universe[0]) }
                val mask = ordinary.filter { random.nextBoolean() }.toSet()
                val tail = listOf(Tail.STAR, Tail.ANY, Tail.ANY_TAINT)[random.nextInt(3)]
                val e = if (tail == Tail.ANY) empty else listOf(empty, ExclusionSet.of(f),
                    ExclusionSet.of(g), ExclusionSet.of(intArrayOf(f, g)))[random.nextInt(4)]
                tree(ordinary, mask, tail, e, Layer.entries[random.nextInt(2)])
            }
            checkSequence(inputs + inputs.take(10))
        }
    }

    @Test fun `generic merge keeps one homogeneous class and rejects cross class inputs`() {
        val a = c(listOf(f))
        val b = c(listOf(g), mark = u)
        val (stored, delta) = m.mergeAddDelta(tree(setOf(a), setOf(a)), tree(setOf(a, b), setOf(a, b)))
        assertEquals((stored as TaintTree).root, stored.nonSubsumable)
        assertEquals(setOf(b), coordinates((delta as TaintTree).root))
        assertEquals(delta.root, delta.nonSubsumable)
        assertFailsWith<IllegalStateException> { m.mergeAddDelta(tree(setOf(a)), tree(setOf(a), setOf(a))) }
    }

    @Test fun `general constructors trim a producer mask by exact coordinates`() {
        val a = c(listOf(f))
        val b = c(listOf(g), mark = u)
        val wrongKind = c(listOf(f), false)
        val mask = root(setOf(a, b, wrongKind))
        assertEquals(setOf(a), coordinates(tree(setOf(a)).withProtection(mask).nonSubsumable))
        assertEquals(setOf(a), coordinates(m.taintTree(x, Layer.NORMAL, root(setOf(a)), nonSubsumable = mask).nonSubsumable))
    }

    @Test fun `cancellation is checked before owner mutation`() {
        val group = TaintGroup(m, m.newInterners().taint)
        val input = tree(setOf(c(listOf(f))))
        fixture.cancellation.cancel()
        assertFailsWith<Cancellation.Cancelled> { group.addAll(input) }
        fixture.cancellation.activate()
        assertTrue(group.all().none())
        assertEquals(listOf(input), group.addAll(input))
    }
}
