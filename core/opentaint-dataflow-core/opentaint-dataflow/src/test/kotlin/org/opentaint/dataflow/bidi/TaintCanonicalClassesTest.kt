package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import kotlin.test.*

class TaintCanonicalClassesTest {
    private val f = StoreFixtures()
    private val m = f.manager
    private val a = f.field("a")
    private val b = f.field("b")
    private val c = f.field("c")
    private fun must(path: List<Int> = emptyList(), e: ExclusionSet = ExclusionSet.Empty) =
        f.fact(path = path, tail = Tail.ANY_TAINT, exclusion = e) as TaintTree
    private fun canonical(inputs: List<TaintTree>): Set<Pattern> {
        val group = TaintGroup(m, m.newInterners().taint)
        inputs.forEach { group.addAll(it) }
        return group.all().flatMap { f.ops.leaves(it) }.toSet()
    }

    @Test fun `ancestor MUST covers admitted descendant with different exclusions in both orders`() {
        val parent = must(e = ExclusionSet.of(a))
        val child = must(listOf(b, c), ExclusionSet.of(c))
        val expected = f.ops.leaves(parent).toSet()
        assertEquals(expected, canonical(listOf(parent, child)))
        assertEquals(expected, canonical(listOf(child, parent)))
    }

    @Test fun `equal coordinate MUST union intersects exclusions without enumerating marks`() {
        val left = must(e = ExclusionSet.of(intArrayOf(a, b)))
        val right = must(e = ExclusionSet.of(intArrayOf(a, c)))
        val expected = f.ops.leaves(must(e = ExclusionSet.of(a))).toSet()
        assertEquals(expected, canonical(listOf(left, right)))
        assertEquals(expected, canonical(listOf(right, left)))
    }

    @Test fun `complete immediate child fills hole but partial and deeper children do not`() {
        val parent = must(e = ExclusionSet.of(a))
        val child = must(listOf(a))
        val expected = f.ops.leaves(must()).toSet()
        assertEquals(expected, canonical(listOf(parent, child)))
        assertEquals(expected, canonical(listOf(child, parent)))
        for (incomplete in listOf(must(listOf(a), ExclusionSet.of(b)), must(listOf(a, b)))) {
            assertEquals(f.ops.leaves(parent).toSet() + f.ops.leaves(incomplete).toSet(),
                canonical(listOf(parent, incomplete)))
        }
    }

    @Test fun `one mixed path packet is canonicalized just like separate offers`() {
        val parent = must()
        val child = must(listOf(a, b))
        val packet = m.taintTree(parent.base, parent.layer,
            m.taintAlg.mergeAdd(parent.root, child.root), anyTail = Tail.ANY_TAINT)
        // Self coverage in a single trie must remove descendant leaves too.
        assertEquals(f.ops.leaves(parent).toSet(), canonical(listOf(packet)))
    }
    @Test fun `MAY same-head exact sibling obeys the existing cross-tail law within one packet`() {
        val may = f.fact(tail = Tail.ANY, layer = Layer.DEMAND) as TaintTree
        val exact = f.fact(layer = Layer.DEMAND) as TaintTree
        val mixed = m.taintTree(may.base, may.layer,
            m.taintAlg.mergeAdd(may.root, exact.root), anyTail = Tail.ANY)
        val group = TaintGroup(m, m.newInterners().taint)
        group.addAll(mixed)
        assertEquals(setOf(may), group.all().toSet())
        assertTrue(group.addAll(exact).isEmpty())
    }

}
