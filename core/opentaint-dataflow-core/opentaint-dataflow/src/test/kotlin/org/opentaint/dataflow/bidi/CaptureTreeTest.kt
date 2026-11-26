package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.CaptureTreeStore
import kotlin.random.Random
import kotlin.test.*

/**
 * R2 of spec/backward-condition-progress-implementation.md §5.7 (1), (2): the meet, the normal form and the trie
 * insert of the capture tree (spec backward-condition-progress §I.3, Lean BackCondImpl, BackND.insertLeaf).
 */
class CaptureTreeTest {
    private val store = StoreFixtures()
    private val m = store.manager
    private val ops = ApOps(m)
    private val x = AccessPathBase.Argument(0)
    private val ret = AccessPathBase.Return
    private val f = m.accessors.index(FieldAccessor("Box", "f", "Box"))
    private val g = m.accessors.index(FieldAccessor("Box", "g", "Box"))
    private val h = m.accessors.index(FieldAccessor("Box", "h", "Box"))
    private val t = m.marks.mark("T")
    private val u = m.marks.mark("U")
    private val forward = ApMode(false, Direction.FORWARD, 4)
    private val method = store.key()
    private val statement = store.inst(1)

    private enum class Kind { EXACT, ANY }
    private data class Leaf(val sigma: List<Int>, val kind: Kind)

    private fun literal(base: AccessPathBase, path: List<Int>, mark: TaintMark = t,
                        exclusion: ExclusionSet = ExclusionSet.Empty) =
        Pattern(PathFact(base, path, Tail.ANY, MarkSlot.Concrete(mark)), exclusion)

    /** One leaf of an input: `$` or `[any-taint]` (a NORMAL STAR read) with an exclusion. */
    private fun input(base: AccessPathBase, path: List<Int>, tail: Tail, mark: TaintMark = t,
                      exclusion: ExclusionSet = ExclusionSet.Empty): Facts =
        m.factsOf(PathFact(base, path, tail, MarkSlot.Concrete(mark)), exclusion, Layer.NORMAL)

    private fun key(literal: Pattern) = CaptureKey(method, statement, "rule", literal)

    /** The completed-combination input: the checked piece of [facts] (code fact F3). */
    private fun checked(facts: Facts, literal: Pattern): Facts? =
        (ops.checkMark(facts, literal, forward) as? MarkCheck.Holds)?.facts

    private fun leaves(tree: TaintNode?): Set<Leaf> = buildSet {
        if (tree == null) return@buildSet
        m.taintAlg.forEachLeaf(tree, EMPTY_PATH) { sigma, leaf ->
            if (leaf.hasAny) {
                assertTrue(leaf.exact.isEmpty, "a capture leaf is one kind")
                add(Leaf(sigma.toList(), Kind.ANY))
            } else add(Leaf(sigma.toList(), Kind.EXACT))
        }
    }

    private fun capture(literal: Pattern, vararg inputs: Facts): Set<Leaf> {
        val captures = CaptureTreeStore(m)
        for (value in inputs) captures.addSink(key(literal), checked(value, literal))
        return leaves(captures.sinkTrees()[key(literal)])
    }

    @Test fun `m1 m2 an input below the literal keeps its leaf kind`() {
        assertEquals(setOf(Leaf(listOf(f), Kind.EXACT)), capture(literal(ret, emptyList()), input(ret, listOf(f), Tail.EXACT)))
        assertEquals(setOf(Leaf(listOf(f), Kind.ANY)), capture(literal(ret, emptyList()), input(ret, listOf(f), Tail.ANY_TAINT)))
    }

    @Test fun `m3 t2 an input above the literal gives the literal itself`() {
        assertEquals(setOf(Leaf(emptyList(), Kind.ANY)), capture(literal(ret, listOf(f)), input(ret, emptyList(), Tail.ANY_TAINT)))
    }

    @Test fun `m4 mark_other an input with another mark is not stored`() {
        assertEquals(emptySet(), capture(literal(ret, emptyList()), input(ret, listOf(f), Tail.EXACT, mark = u)))
    }

    @Test fun `t1 meet first and leaves only drop the input exclusion`() {
        val lit = literal(x, emptyList())
        assertEquals(setOf(Leaf(listOf(f, g), Kind.EXACT), Leaf(listOf(h), Kind.ANY)), capture(lit,
            input(x, listOf(f, g), Tail.EXACT), input(x, listOf(h), Tail.ANY_TAINT, exclusion = ExclusionSet.of(intArrayOf(g)))))
    }

    @Test fun `t3 t4 one tree subsumes a deeper exact leaf and keeps an equal leaf once`() {
        val lit = literal(x, emptyList())
        val any = input(x, listOf(f), Tail.ANY_TAINT)
        val deep = input(x, listOf(f, g), Tail.EXACT)
        val other = input(x, listOf(h), Tail.EXACT)
        val expected = setOf(Leaf(listOf(f), Kind.ANY), Leaf(listOf(h), Kind.EXACT))
        assertEquals(expected, capture(lit, any, deep, other))
        assertEquals(expected, capture(lit, deep, other, any))
        val captures = CaptureTreeStore(m)
        captures.addSink(key(lit), checked(input(x, listOf(g), Tail.EXACT), lit))
        val first = captures.sinkTrees().getValue(key(lit))
        captures.addSink(key(lit), checked(input(x, listOf(g), Tail.EXACT), lit))
        assertSame(first, captures.sinkTrees().getValue(key(lit)), "an equal leaf changes nothing")
        assertEquals(setOf(Leaf(listOf(g), Kind.EXACT)), leaves(first))
    }

    @Test fun `star_start a STAR input below the literal gives an any leaf at the cut`() {
        val star = m.factsOf(PathFact(x, listOf(f), Tail.STAR, MarkSlot.Concrete(t)), ExclusionSet.Empty, Layer.NORMAL)
        assertEquals(setOf(Leaf(listOf(f), Kind.ANY)), capture(literal(x, emptyList()), star))
    }

    @Test fun `spine_excl a spine any leaf that excludes the literal field gives no leaf`() {
        val lit = literal(x, listOf(f))
        assertEquals(setOf(Leaf(listOf(g), Kind.EXACT)), capture(lit,
            input(x, listOf(f, g), Tail.EXACT), input(x, emptyList(), Tail.ANY_TAINT, exclusion = ExclusionSet.of(intArrayOf(f)))))
        assertEquals(setOf(Leaf(emptyList(), Kind.ANY)), capture(lit,
            input(x, listOf(f, g), Tail.EXACT), input(x, emptyList(), Tail.ANY_TAINT, exclusion = ExclusionSet.of(intArrayOf(g)))))
    }

    @Test fun `flow_none a FLOW or REACH input and a literal out of scope store nothing`() {
        val lit = literal(x, emptyList())
        val captures = CaptureTreeStore(m)
        captures.addSink(key(lit), m.flowTree(x, Layer.NORMAL, ExclusionSet.Empty, MarkSet.EMPTY, FlowAlgebra.LEAF_NODE))
        captures.addSink(key(lit), Reach.of(Layer.NORMAL))
        captures.addSink(key(lit), null)
        assertTrue(captures.sinkTrees().isEmpty())
        // C7: only [any] literals with an empty exclusion and a FULL concrete mark.
        val exact = Pattern(PathFact(x, emptyList(), Tail.EXACT, MarkSlot.Concrete(t)), ExclusionSet.Empty)
        val excluded = literal(x, emptyList(), exclusion = ExclusionSet.of(intArrayOf(g)))
        val grouped = literal(x, emptyList(), mark = m.marks.group(m.marks.groupOf(t)))
        for (p in listOf(exact, excluded, grouped)) captures.addSource(key(p), input(x, listOf(f), Tail.EXACT))
        assertTrue(captures.sourceTrees().isEmpty())
    }

    @Test fun `treeSeed puts the tree below the literal path with the literal mark and DEMAND`() {
        val lit = literal(x, listOf(f))
        val captures = CaptureTreeStore(m)
        captures.addSink(key(lit), checked(input(x, listOf(f, g), Tail.EXACT), lit))
        captures.addSink(key(lit), checked(input(x, listOf(f, h), Tail.ANY_TAINT), lit))
        val literalFact = ops.targetTree(lit.fact, Layer.DEMAND) as TaintTree
        val seed = m.treeSeed(literalFact, lit.fact.path, captures.sinkTrees().getValue(key(lit)))
        assertEquals(Layer.DEMAND, seed.layer)
        assertEquals(setOf(Conclusion(PathFact(x, listOf(f, g), Tail.EXACT, MarkSlot.Concrete(t)), ExclusionSet.Empty, true),
            Conclusion(PathFact(x, listOf(f, h), Tail.ANY, MarkSlot.Concrete(t)), ExclusionSet.Empty, true)),
            ops.leaves(seed).map { Conclusion(it.fact, it.exclusion, true) }.toSet())
    }

    @Test fun `mergeCapture inserts each leaf of the second tree`() {
        val lit = literal(x, emptyList())
        val a = CaptureTreeStore(m).also { it.addSink(key(lit), checked(input(x, listOf(f, g), Tail.EXACT), lit)) }
        val b = CaptureTreeStore(m).also {
            it.addSink(key(lit), checked(input(x, listOf(f), Tail.ANY_TAINT), lit))
            it.addSink(key(lit), checked(input(x, listOf(h), Tail.EXACT), lit))
        }
        val merged = m.mergeCapture(a.sinkTrees().getValue(key(lit)), b.sinkTrees().getValue(key(lit)), lit)
        assertEquals(setOf(Leaf(listOf(f), Kind.ANY), Leaf(listOf(h), Kind.EXACT)), leaves(merged))
    }

    /** A Kotlin copy of Lean BackND.insertLeaf on a list of (σ, kind). */
    private fun referenceInsert(list: List<Leaf>, leaf: Leaf): List<Leaf> {
        fun prefix(a: List<Int>, b: List<Int>) = a.size <= b.size && b.subList(0, a.size) == a
        return when {
            list.any { it.kind == Kind.ANY && prefix(it.sigma, leaf.sigma) } -> list
            leaf.kind == Kind.EXACT && leaf in list -> list
            leaf.kind == Kind.ANY -> list.filterNot { prefix(leaf.sigma, it.sigma) } + leaf
            else -> list + leaf
        }
    }

    private fun covered(leaves: Collection<Leaf>, universe: List<List<Int>>): Set<List<Int>> = universe.filterTo(HashSet()) { p ->
        leaves.any { l -> if (l.kind == Kind.EXACT) l.sigma == p else p.size >= l.sigma.size && p.subList(0, l.sigma.size) == l.sigma }
    }

    @Test fun `trie insert agrees with the list reference and does not depend on the arrival order`() {
        val fields = listOf(f, g, h)
        val universe = buildList {
            add(emptyList<Int>())
            for (a in fields) { add(listOf(a)); for (b in fields) { add(listOf(a, b)); for (c in fields) add(listOf(a, b, c)) } }
        }
        val random = Random(20261126)
        val lit = literal(x, emptyList())
        var nonTrivial = 0
        repeat(2000) {
            val leaves = List(random.nextInt(1, 8)) {
                Leaf(List(random.nextInt(0, 4)) { fields[random.nextInt(fields.size)] }, if (random.nextInt(3) == 0) Kind.ANY else Kind.EXACT)
            }
            fun trie(order: List<Leaf>): TaintNode? {
                var tree: TaintNode? = null
                for (leaf in order) tree = m.captureLeaf(tree, leaf.sigma.toIntArray(), leaf.kind == Kind.ANY, lit)
                return tree
            }
            val reference = leaves.fold(emptyList<Leaf>(), ::referenceInsert)
            val actual = trie(leaves)
            assertEquals(reference.toSet(), leaves(actual), "leaves=$leaves")
            val shuffled = trie(leaves.shuffled(random))
            assertEquals(covered(reference, universe), covered(leaves(shuffled), universe), "leaves=$leaves")
            if (reference.size < leaves.toSet().size) nonTrivial++
        }
        assertTrue(nonTrivial > 100, "the random leaves exercise subsumption ($nonTrivial)")
    }
}
