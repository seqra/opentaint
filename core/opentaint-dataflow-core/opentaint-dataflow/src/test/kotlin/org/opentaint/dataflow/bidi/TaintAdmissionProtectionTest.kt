package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.util.Cancellation
import kotlin.random.Random
import kotlin.test.*

/** Compare every emitted and retained annotated value with the old scalar admission. */
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
    private data class AnnotatedRow(
        val base: AccessPathBase, val layer: Layer, val exclusion: ExclusionSet, val tail: Tail,
        val ordinary: Set<Coordinate>, val protected: Set<Coordinate>,
    )

    private fun c(path: List<Int>, exact: Boolean = true, mark: TaintMark = t) =
        Coordinate(path, exact, mark.id)

    private fun root(coordinates: Collection<Coordinate>): TaintNode {
        check(coordinates.isNotEmpty())
        return coordinates.map {
            val marks = MarkSet(intArrayOf(it.mark))
            val leaf = if (it.exact) m.taintLeaves(marks, MarkSet.EMPTY)
                else m.taintLeaves(MarkSet.EMPTY, marks)
            m.taintAlg.prepend(m, m.path(it.path), m.taintAlg.leafNode(leaf))
        }.reduce { a, b -> m.taintAlg.mergeAdd(a, b, m.cancellation) }
    }

    private fun tree(coordinates: Set<Coordinate>, protected: Set<Coordinate> = emptySet(),
                     tail: Tail = Tail.ANY_TAINT, exclusion: ExclusionSet = empty,
                     layer: Layer = Layer.NORMAL): TaintTree =
        m.taintTree(x, layer, root(coordinates), exclusion, tail,
            nonSubsumable = protected.takeIf { it.isNotEmpty() }?.let(::root))

    private fun coordinates(root: TaintNode?): Set<Coordinate> = buildSet {
        if (root == null) return@buildSet
        val pending = ArrayDeque<Pair<List<Int>, TaintNode>>()
        pending += emptyList<Int>() to root
        while (pending.isNotEmpty()) {
            val (path, node) = pending.removeLast()
            node.leaf.exact.ids.forEach { add(Coordinate(path, true, it)) }
            node.leaf.any.ids.forEach { add(Coordinate(path, false, it)) }
            val accessors = node.accessors
            val children = node.children
            if (accessors != null && children != null) for (i in accessors.indices)
                pending += (path + accessors[i]) to children[i]
        }
    }

    private fun observed(t: TaintTree?): AnnotatedRow? = t?.let {
        AnnotatedRow(it.base, it.layer, it.exclusion, it.anyTail,
            coordinates(it.root), coordinates(it.nonSubsumable))
    }

    private fun checkSequence(inputs: List<TaintTree>): List<TaintTree?> {
        val actual = TaintGroup(m, m.newInterners().taint)
        val reference = ReferenceTaintGroup(m, m.newInterners().taint)
        return inputs.mapIndexed { i, input ->
            val old = reference.add(input)
            val new = actual.add(input)
            assertEquals(observed(old), observed(new), "delta $i of ${inputs.map(::observed)}")
            assertEquals(reference.all().map(::observed).toList(), actual.all().map(::observed).toList(),
                "stored rows at $i")
            actual.all().forEach {
                assertTrue(coordinates(it.root).containsAll(coordinates(it.nonSubsumable)))
            }
            new
        }
    }

    @Test
    fun `ordinary merge preserves partial masks and emits only fresh memberships`() {
        val a = c(listOf(f))
        val b = c(listOf(g), mark = u)
        val common = c(emptyList(), mark = u)
        val deltas = checkSequence(listOf(tree(setOf(a, common), setOf(a)),
            tree(setOf(b, common), setOf(b))))
        assertEquals(setOf(b), coordinates(deltas[1]!!.root))
        assertEquals(setOf(b), coordinates(deltas[1]!!.nonSubsumable))
    }

    @Test
    fun `protection only upgrades are emitted once and never downgraded`() {
        val a = c(listOf(f))
        val plain = tree(setOf(a))
        val protected = tree(setOf(a), setOf(a))
        val deltas = checkSequence(listOf(plain, plain, protected, plain, protected))
        assertNotNull(deltas[0])
        assertNull(deltas[1])
        assertEquals(setOf(a), coordinates(deltas[2]!!.nonSubsumable))
        assertNull(deltas[3])
        assertNull(deltas[4])
    }

    @Test
    fun `ordinary ANY cover cannot remove a new protected exact coordinate`() {
        val parent = c(emptyList(), exact = false)
        val exact = c(listOf(f))
        val deltas = checkSequence(listOf(
            tree(setOf(parent), tail = Tail.ANY, layer = Layer.DEMAND),
            tree(setOf(exact), setOf(exact), layer = Layer.DEMAND)))
        assertEquals(setOf(exact), coordinates(deltas[1]!!.root))
        assertEquals(setOf(exact), coordinates(deltas[1]!!.nonSubsumable))
    }

    @Test
    fun `equal ordinary roots use the new intersected exclusion and union masks`() {
        val a = c(listOf(f), exact = false)
        val b = c(listOf(g), exact = false, mark = u)
        val aTree = tree(setOf(a, b), setOf(a), exclusion = ExclusionSet.of(f))
        val bTree = tree(setOf(a, b), setOf(b), exclusion = ExclusionSet.of(g))
        val delta = checkSequence(listOf(aTree, bTree))[1]!!
        assertEquals(empty, delta.exclusion)
        assertEquals(setOf(a, b), coordinates(delta.nonSubsumable))
    }

    @Test
    fun `equal root with unchanged exclusion retains a fresh protected membership`() {
        val a = c(listOf(f), exact = false)
        val b = c(listOf(g), exact = false, mark = u)
        val broad = tree(setOf(a, b), setOf(a), exclusion = ExclusionSet.of(f))
        val narrower = tree(setOf(a, b), setOf(b), exclusion = ExclusionSet.of(intArrayOf(f, g)))
        val delta = checkSequence(listOf(broad, narrower))[1]!!
        assertEquals(setOf(b), coordinates(delta.nonSubsumable))
    }

    @Test
    fun `removing the last must coordinate canonicalizes exact header and preserves its mask`() {
        val must = c(emptyList(), exact = false)
        val exact = c(listOf(g))
        val delta = checkSequence(listOf(
            tree(setOf(must), exclusion = ExclusionSet.of(f)),
            tree(setOf(must, exact), setOf(exact), exclusion = ExclusionSet.of(intArrayOf(f, g)))))[1]!!
        assertEquals(setOf(exact), coordinates(delta.root))
        assertEquals(setOf(exact), coordinates(delta.nonSubsumable))
        assertEquals(empty, delta.exclusion)
        assertEquals(Tail.ANY_TAINT, delta.anyTail)
    }

    @Test
    fun `interned equivalent roots preserve masks and independent layers`() {
        val a = c(listOf(f), exact = false)
        val b = c(listOf(g), mark = u)
        val normal = tree(setOf(a, b), setOf(a), tail = Tail.STAR, exclusion = ExclusionSet.of(g))
        val demand = tree(setOf(a, b), setOf(b), tail = Tail.STAR,
            exclusion = ExclusionSet.of(g), layer = Layer.DEMAND)
        checkSequence(listOf(normal, demand, tree(setOf(a, b), setOf(a), tail = Tail.STAR,
            exclusion = ExclusionSet.of(g)), demand))
    }

    @Test
    fun `finite typed cells agree for every ordered pair`() {
        val a = c(listOf(f))
        val b = c(listOf(g), exact = false, mark = u)
        val cells = buildList {
            for (layer in Layer.entries) for (tail in listOf(Tail.STAR, Tail.ANY, Tail.ANY_TAINT)) {
                for (e in if (tail == Tail.ANY) listOf(empty) else listOf(empty, ExclusionSet.of(f))) {
                    for (ordinary in listOf(setOf(a), setOf(b), setOf(a, b))) {
                        for (mask in listOf(emptySet(), setOf(ordinary.first()), ordinary))
                            add(tree(ordinary, mask, tail, e, layer))
                    }
                }
            }
        }
        for (first in cells) for (second in cells) checkSequence(listOf(first, second))
    }

    @Test
    fun `mixed repeated admissions agree after every delta and retained row`() {
        val random = Random(734279)
        val universe = listOf(c(emptyList()), c(listOf(f)), c(listOf(g), mark = u),
            c(emptyList(), exact = false), c(listOf(f), exact = false),
            c(listOf(g, f), exact = false, mark = u))
        repeat(40) {
            val values = List(60) {
                val ordinary = universe.filter { random.nextBoolean() }.toSet().ifEmpty { setOf(universe[0]) }
                val mask = ordinary.filter { random.nextBoolean() }.toSet()
                val tail = listOf(Tail.STAR, Tail.ANY, Tail.ANY_TAINT)[random.nextInt(3)]
                val e = if (tail == Tail.ANY) empty else listOf(empty, ExclusionSet.of(f),
                    ExclusionSet.of(g), ExclusionSet.of(intArrayOf(f, g)))[random.nextInt(4)]
                tree(ordinary, mask, tail, e, Layer.entries[random.nextInt(2)])
            }
            checkSequence(values + values.take(10))
        }
    }

    @Test
    fun `general constructors still trim masks by exact coordinates`() {
        val a = c(listOf(f))
        val b = c(listOf(g), mark = u)
        val wrongKind = c(listOf(f), exact = false)
        val input = tree(setOf(a, b), setOf(a, b))
        val mask = root(setOf(a, b, wrongKind))
        assertEquals(setOf(a), coordinates(input.withRoot(root(setOf(a))).nonSubsumable))
        assertEquals(setOf(a), coordinates(tree(setOf(a)).withProtection(mask).nonSubsumable))
        assertEquals(setOf(a), coordinates(m.taintTree(x, Layer.NORMAL, root(setOf(a)),
            nonSubsumable = mask).nonSubsumable))
    }

    @Test
    fun `generic delta trims the merged mask instead of assuming it belongs to delta`() {
        val a = c(listOf(f))
        val b = c(listOf(g), mark = u)
        val (stored, delta) = m.mergeAddDelta(tree(setOf(a), setOf(a)),
            tree(setOf(a, b), setOf(a)))
        assertEquals(setOf(a), coordinates((stored as TaintTree).nonSubsumable))
        assertEquals(setOf(b), coordinates((delta as TaintTree).root))
        assertNull(delta.nonSubsumable)
    }

    @Test
    fun `certified admission bytecode contains no generic mask normalization calls`() {
        // This is a cost regression guard. Value equivalence alone cannot detect a
        // redundant trim that returns the same valid mask. Keep general trims elsewhere.
        val packagePath = "/org/opentaint/dataflow/bidi/ap/"
        for (name in listOf("TaintGroup", "GroupsKt")) {
            val bytes = assertNotNull(TaintGroup::class.java.getResourceAsStream("$packagePath$name.class"))
                .use { it.readBytes().toString(Charsets.ISO_8859_1) }
            for (call in listOf("intersectTaintMask", "withProtection", "withRoot", "taintTree"))
                assertFalse(call in bytes, "$name still references generic normalization $call")
        }
    }

    @Test
    fun `admission still checks cancellation before changing state`() {
        val group = TaintGroup(m, m.newInterners().taint)
        val input = tree(setOf(c(listOf(f))))
        fixture.cancellation.cancel()
        assertFailsWith<Cancellation.Cancelled> { group.add(input) }
        fixture.cancellation.activate()
        assertEquals(emptyList(), group.all().toList())
        assertNotNull(group.add(input))
    }
}

/** The reviewed base admission, kept only as the differential test oracle. */
private class ReferenceTaintGroup(private val m: ApManager, private val interner: TrieInterner<TaintLeaves>) {
    private val trees = arrayOf(ArrayList<TaintTree>(1), ArrayList<TaintTree>(1))

    fun all(): Sequence<TaintTree> = trees[0].asSequence() + trees[1].asSequence()

    /** Restore one complete current typed header for a temporary admission
     * adapter. Do not re-admit the snapshot: that would compact old STAR rows
     * merely because a later ANY row is already present. No history is kept. */
    internal fun restoreCurrent(t: TaintTree) {
        m.cancellation.checkpoint()
        val list = trees[t.layer.ordinal]
        check(list.none { it.anyTail == t.anyTail && it.exclusion == t.exclusion })
        list += t
    }

    fun add(t: TaintTree): TaintTree? {
        val alg = m.taintAlg
        val list = trees[t.layer.ordinal]
        var pending = t
        while (true) {
            m.cancellation.checkpoint()
            val sameKey = list.indexOfFirst {
                m.cancellation.checkpoint()
                it.anyTail == pending.anyTail && it.exclusion == pending.exclusion
            }
            if (sameKey < 0) {
                val k = list.indexOfFirst {
                    m.cancellation.checkpoint()
                    it.anyTail == pending.anyTail && it.root == pending.root
                }
                if (k >= 0) {
                    val stored = list[k]
                    val exclusion = stored.exclusion.intersect(pending.exclusion)
                    // Equal ordinary content can still carry a new protected membership.
                    if (exclusion == stored.exclusion) {
                        val rest = subtractSubsumed(pending, list) ?: return null
                        val protection = mergeProtection(stored.nonSubsumable, rest.nonSubsumable)
                        val root = alg.mergeAdd(stored.root, rest.root, m.cancellation)
                        list[k] = stored.withRoot(interner.internIfRequired(root)).withProtection(protection)
                        return rest
                    }
                    list.removeAt(k)
                    pending = m.taintTree(pending.base, pending.layer, stored.root, exclusion, pending.anyTail)
                        .withProtection(mergeProtection(stored.nonSubsumable, pending.nonSubsumable))
                    continue
                }
            }

            val rest = subtractSubsumed(pending, list) ?: return null
            // Subtraction can remove the last must leaf. Its canonical key is then Empty E.
            val i = list.indexOfFirst {
                m.cancellation.checkpoint()
                it.anyTail == rest.anyTail && it.exclusion == rest.exclusion
            }
            if (i < 0) {
                list += rest.withRoot(interner.internIfRequired(rest.root))
                return rest
            }
            val stored = list[i]
            val (merged, delta) = alg.mergeAddDelta(stored.root, rest.root, m.cancellation)
            val protection = mergeProtection(stored.nonSubsumable, rest.nonSubsumable)
            val deltaRoot = mergeProtection(delta, rest.nonSubsumable) ?: return null
            list[i] = stored.withRoot(interner.internIfRequired(merged)).withProtection(protection)
            return m.taintTree(pending.base, pending.layer, deltaRoot, rest.exclusion, rest.anyTail)
                .withProtection(rest.nonSubsumable)
        }
    }

    private fun subtractSubsumed(t: TaintTree, others: List<TaintTree>): TaintTree? {
        val ordinary = subtract(t.root, t, others, protectedOnly = false)
        // Ordinary ANY coverage cannot consume a fresh protected EXACT dependency.
        val protection = t.nonSubsumable?.let { subtract(it, t, others, protectedOnly = true) }
        val root = mergeProtection(ordinary, protection) ?: return null
        if (root === t.root && protection === t.nonSubsumable) return t
        return t.withRoot(root).withProtection(protection)
    }

    private fun mergeProtection(a: TaintNode?, b: TaintNode?): TaintNode? = when {
        a == null -> b
        b == null -> a
        else -> m.taintAlg.mergeAdd(a, b, m.cancellation)
    }

    private fun subtract(root: TaintNode, t: TaintTree, others: List<TaintTree>,
                         protectedOnly: Boolean): TaintNode? {
        val alg = m.taintAlg
        var remaining = root
        for (stored in others) {
            m.cancellation.checkpoint()
            val storedRoot = if (protectedOnly) stored.nonSubsumable ?: continue else stored.root
            val storedMay = stored.anyTail == Tail.ANY
            val storedStar = stored.anyTail == Tail.STAR
            val coversAny = storedMay || stored.anyTail == t.anyTail
            val anyAt = coversAny && (storedMay || stored.exclusion.isSubsetOf(t.exclusion))
            remaining = alg.subtract(remaining, storedRoot, TaintLeaves.EMPTY,
                at = { alg.leaves(if (storedMay) it.exact + it.any else it.exact,
                    if (anyAt) it.any else MarkSet.EMPTY) },
                below = { alg.leaves(if (storedMay) it.any else MarkSet.EMPTY,
                    if (coversAny && !storedStar) it.any else MarkSet.EMPTY) },
                admits = stored.exclusion::admits,
                cancellation = m.cancellation) ?: return null
        }
        return remaining
    }
}

