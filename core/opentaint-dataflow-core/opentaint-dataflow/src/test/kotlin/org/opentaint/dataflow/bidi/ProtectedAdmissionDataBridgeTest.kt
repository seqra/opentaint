package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import kotlin.test.*

/** Incremental bridge checks, not a batch normal form or a confluence oracle.
 * Every trial restores the SAME current rows on both sides. Its DATA baseline
 * erases H, restores those rows without admission, and performs ONE no-H add.
 * This deliberately includes the selected DEMAND/ANY position law; the older
 * ReferenceTaintGroup compacts those positions and is not its oracle.
 *
 * H and guide expectations are independently decoded literal typed unions.
 * DATA observations enumerate f/g/h paths through depth 3 for full marks T/U;
 * they are finite spatial regions, not a universal STAR suffix-relation proof.
 * Explicit STAR/T4 and mixed-header witnesses supplement that bounded view.
 * This class does not establish all adapters, program recovery or global DATA
 * order independence. The production no-H path is the differential DATA
 * baseline, never the expected-H oracle.
 */
class ProtectedAdmissionDataBridgeTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val x = AccessPathBase.Argument(0)
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val h = fixture.field("h")
    private val t = fixture.mark("T").id
    private val u = fixture.mark("U").id
    private val empty = ExclusionSet.Empty

    private data class Atom(val path: List<Int>, val exact: Boolean, val mark: Int)
    private fun exact(path: List<Int>, mark: Int = t) = Atom(path, true, mark)
    private fun span(path: List<Int>, mark: Int = t) = Atom(path, false, mark)
    private fun ex(vararg fields: Int) = ExclusionSet.of(fields)

    private class RawNode {
        val exact = sortedSetOf<Int>()
        val any = sortedSetOf<Int>()
        val children = sortedMapOf<Int, RawNode>()
    }

    private fun root(atoms: Set<Atom>): TaintNode {
        require(atoms.isNotEmpty())
        val root = RawNode()
        for (atom in atoms) {
            var node = root
            for (field in atom.path) node = node.children.getOrPut(field) { RawNode() }
            if (atom.exact) node.exact += atom.mark else node.any += atom.mark
        }
        fun build(node: RawNode): TaintNode = m.taintAlg.node(
            m.taintLeaves(MarkSet(node.exact.toIntArray()), MarkSet(node.any.toIntArray())),
            node.children.keys.toIntArray(), node.children.values.map(::build).toTypedArray())
        return build(root)
    }

    private fun tree(atoms: Set<Atom>, flags: Set<Atom> = emptySet(),
                     tail: Tail = Tail.STAR, e: ExclusionSet = empty,
                     layer: Layer = Layer.NORMAL): TaintTree {
        require(atoms.containsAll(flags))
        require(tail != Tail.ANY || e == empty)
        return m.taintTree(x, layer, root(atoms), e, tail,
            nonSubsumable = flags.takeIf { it.isNotEmpty() }?.let(::root))
    }

    /** Direct sparse-DAG inspection; no leaves(), covers(), subtraction,
     * canonicalizer or protection attachment is used to form expected keys. */
    private fun atoms(root: TaintNode?): Set<Atom> = buildSet {
        if (root == null) return@buildSet
        val todo = ArrayDeque<Pair<List<Int>, TaintNode>>()
        todo.addLast(emptyList<Int>() to root)
        while (todo.isNotEmpty()) {
            val (path, node) = todo.removeLast()
            node.leaf.exact.ids.forEach { add(exact(path, it)) }
            node.leaf.any.ids.forEach { add(span(path, it)) }
            val fields = node.accessors
            val children = node.children
            if (fields != null && children != null) for (i in fields.indices)
                todo.addLast((path + fields[i]) to children[i])
        }
    }

    private data class Key(val base: AccessPathBase, val layer: Layer,
                           val path: List<Int>, val mark: Int,
                           val tail: Tail, val e: ExclusionSet)

    private fun key(value: TaintTree, atom: Atom) = Key(value.base, value.layer,
        atom.path, atom.mark, if (atom.exact) Tail.EXACT else value.anyTail,
        if (atom.exact) empty else value.exclusion)

    private fun keys(values: List<TaintTree>, flags: Boolean = false): Set<Key> = buildSet {
        for (value in values) for (atom in atoms(if (flags) value.nonSubsumable else value.root))
            add(key(value, atom))
    }

    private fun guides(values: List<TaintTree>): Set<Key> = keys(values).filterTo(HashSet()) {
        it.layer == Layer.DEMAND && it.tail == Tail.ANY && it.e == empty
    }

    private data class Point(val base: AccessPathBase, val layer: Layer,
                             val path: List<Int>, val mark: Int)
    private val paths = buildList {
        var level = listOf(emptyList<Int>())
        addAll(level)
        repeat(3) {
            level = level.flatMap { p -> listOf(p + f, p + g, p + h) }
            addAll(level)
        }
    }

    /** Independent finite spatial denotation. Effective EXACT ignores mixed
     * wrapper E/tail; a span excludes only its first continuation field. */
    private fun region(values: List<TaintTree>): Set<Point> = buildSet {
        for (value in values) {
            val excluded = when (val e = value.exclusion) {
                ExclusionSet.Empty -> emptySet()
                is ExclusionSet.Concrete -> e.ids.toSet()
            }
            for (atom in atoms(value.root)) for (path in paths) {
                if (atom.exact) {
                    if (path == atom.path) add(Point(value.base, value.layer, path, atom.mark))
                } else if (path.size >= atom.path.size && path.take(atom.path.size) == atom.path &&
                    (path.size == atom.path.size || value.anyTail == Tail.ANY ||
                        path[atom.path.size] !in excluded)) {
                    add(Point(value.base, value.layer, path, atom.mark))
                }
            }
        }
    }

    private data class Observation(val after: List<TaintTree>, val delta: List<TaintTree>,
                                   val dataAfter: List<TaintTree>, val dataDelta: List<TaintTree>)

    private fun step(before: List<TaintTree>, offered: TaintTree, label: String): Observation {
        val protected = TaintGroup(m, m.newInterners().taint)
        val noH = TaintGroup(m, m.newInterners().taint)
        for (current in before) {
            protected.restoreCurrent(current)
            noH.restoreCurrent(current.withoutProtection())
        }
        val dataDelta = noH.addAll(offered.withoutProtection())
        val dataAfter = noH.all().toList()
        val delta = protected.addAll(offered)
        val after = protected.all().toList()

        val beforeRegion = region(before)
        val afterRegion = region(after)
        assertEquals(region(dataAfter), afterRegion, "$label: same restored-state DATA result")
        assertEquals(region(dataDelta) - beforeRegion, region(delta) - beforeRegion,
            "$label: same new DATA region; whole-content deltas may replay old content")
        assertEquals(afterRegion, region(before + delta), "$label: complete DATA delta")
        assertTrue(afterRegion.containsAll(region(delta)), "$label: no delta outside retained DATA")

        val oldH = keys(before, flags = true)
        val expectedH = oldH + keys(listOf(offered), flags = true)
        val actualH = keys(after, flags = true)
        val deltaH = keys(delta, flags = true)
        assertEquals(expectedH, actualH, "$label: literal typed H union")
        assertTrue(expectedH.containsAll(deltaH), "$label: no invented delta H")
        assertEquals(expectedH, oldH + deltaH, "$label: complete typed H delta")

        val oldGuides = guides(before)
        val expectedGuides = oldGuides + guides(listOf(offered))
        assertEquals(expectedGuides, guides(after), "$label: literal selected MAY position union")
        assertTrue(expectedGuides.containsAll(guides(delta)), "$label: no invented guide delta")
        assertEquals(expectedGuides, oldGuides + guides(delta), "$label: complete guide delta")

        for (value in after + delta) assertTrue(atoms(value.root).containsAll(atoms(value.nonSubsumable)),
            "$label: every H bit has a literal same-packet DATA carrier")
        assertEquals(after.size, after.map { it.groupKey }.toSet().size, "$label: unique typed headers")
        return Observation(after, delta, dataAfter, dataDelta)
    }

    private fun sequence(offers: List<TaintTree>, label: String): List<Observation> {
        var current = emptyList<TaintTree>()
        return offers.mapIndexed { i, offered ->
            step(current, offered, "$label/$i").also { current = it.after }
        }
    }

    @Test fun `STAR T4 E weakening keeps the whole mixed-content delta with either H arrival order`() {
        val payload = setOf(span(emptyList()), exact(listOf(g), u))
        val flag = setOf(exact(listOf(g), u))
        for (layer in Layer.entries) for (protectedFirst in listOf(false, true)) {
            val a = tree(payload, flag, Tail.STAR, ex(f), layer)
            val b = tree(payload, tail = Tail.STAR, e = ex(g), layer = layer)
            val offers = if (protectedFirst) listOf(a, b) else listOf(b, a)
            val last = sequence(offers, "STAR T4/$layer/Hfirst=$protectedFirst").last()
            val expected = payload.map { key(tree(payload, tail = Tail.STAR, layer = layer), it) }.toSet()
            assertEquals(expected, keys(last.dataDelta), "Independent old T4 whole-content witness")
            assertEquals(expected, keys(last.delta), "Do not reduce T4 to only its newly admitted span")
            assertTrue(last.delta.any { it.anyTail == Tail.STAR && it.exclusion == empty && atoms(it.root) == payload })
            assertTrue(step(last.after, offers.last(), "STAR duplicate").delta.isEmpty())
        }
    }

    @Test fun `bridge restores existing STAR next to later ANY instead of re-admitting its snapshot`() {
        val oldStar = tree(setOf(span(emptyList())), tail = Tail.STAR, e = ex(f), layer = Layer.DEMAND)
        val laterAny = tree(setOf(span(emptyList())), tail = Tail.ANY, layer = Layer.DEMAND)
        val fresh = exact(listOf(g), u)
        val offered = tree(setOf(fresh), setOf(fresh), layer = Layer.DEMAND)
        // An existing current state is supplied, not a request to canonicalize
        // these two rows as a fresh input batch in either order.
        for (before in listOf(listOf(oldStar, laterAny), listOf(laterAny, oldStar))) {
            val out = step(before, offered, "restored STAR/ANY")
            assertTrue(key(oldStar, span(emptyList())) in keys(out.dataAfter))
            assertTrue(key(oldStar, span(emptyList())) in keys(out.after), "Keep original STAR header/E")
            assertEquals(setOf(key(offered, fresh)), keys(out.delta, flags = true))
        }
    }

    @Test fun `effective EXACT H ignores different mixed wrappers without spreading to spans`() {
        val flag = exact(listOf(g), u)
        val payload = setOf(span(emptyList()), flag)
        for (layer in Layer.entries) {
            val a = tree(payload, setOf(flag), Tail.STAR, ex(f), layer)
            val b = tree(payload, setOf(flag), Tail.ANY_TAINT, ex(h), layer)
            for (offers in listOf(listOf(a, b), listOf(b, a))) {
                val observations = sequence(offers, "EXACT mixed E/$layer")
                assertEquals(setOf(key(a, flag)), keys(observations.last().after, flags = true))
                assertTrue(keys(observations.last().delta, flags = true).isEmpty(), "New wrapper is not new exact H")
                assertEquals(setOf(key(a, span(emptyList())), key(b, span(emptyList()))),
                    keys(observations.last().after).filter { it.tail != Tail.EXACT }.toSet())
            }
        }
    }

    @Test fun `MUST hole fill and E join preserve old DATA while retaining original H headers`() {
        val original = span(emptyList())
        for (layer in Layer.entries) {
            val old = tree(setOf(original), setOf(original), Tail.ANY_TAINT, ex(f), layer)
            val fill = tree(setOf(span(listOf(f))), tail = Tail.ANY_TAINT, layer = layer)
            val otherE = tree(setOf(original), tail = Tail.ANY_TAINT, e = ex(g), layer = layer)
            for ((name, input) in listOf("hole" to fill, "E join" to otherE))
                for (offers in listOf(listOf(old, input), listOf(input, old))) {
                    val out = sequence(offers, "MUST $name/$layer").last()
                    val completed = key(tree(setOf(original), tail = Tail.ANY_TAINT, layer = layer), original)
                    assertTrue(completed in keys(out.dataAfter), "Independent old DATA fill/join witness")
                    assertTrue(completed in keys(out.after), "Retain DATA-derived plain Empty-E span")
                    assertEquals(setOf(key(old, original)), keys(out.after, flags = true), "Do not protect derived E")
                    assertTrue(key(old, original) in keys(out.after), "Original H retains its literal E carrier")
                }
        }
    }

    @Test fun `active DEMAND ANY guides and partial H retain positions in packets and both orders`() {
        val root = span(emptyList())
        val child = span(listOf(f))
        val other = span(listOf(f), u)
        for (protectedAtom in listOf(root, child)) {
            val a = tree(setOf(root), setOf(root).intersect(setOf(protectedAtom)), Tail.ANY, layer = Layer.DEMAND)
            val b = tree(setOf(child, other), setOf(child, other).intersect(setOf(protectedAtom)), Tail.ANY, layer = Layer.DEMAND)
            val packet = tree(setOf(root, child, other), setOf(protectedAtom), Tail.ANY, layer = Layer.DEMAND)
            for (offers in listOf(listOf(a, b), listOf(b, a), listOf(packet))) {
                val out = sequence(offers, "DEMAND ANY partial H/$protectedAtom").last()
                assertEquals(setOf(root, child, other).map { key(packet, it) }.toSet(), guides(out.after))
                assertEquals(setOf(key(packet, protectedAtom)), keys(out.after, flags = true))
                assertTrue(step(out.after, packet, "DEMAND ANY duplicate").delta.isEmpty())
            }
        }
    }
}
