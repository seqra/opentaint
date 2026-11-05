package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import kotlin.random.Random
import kotlin.test.*

/** A finite concrete-position oracle checks exact unions independently of trie reduction. */
class SpatialCanonicalOracleTest {
    @Test fun `MUST admission preserves ordinary and protected regions across mixed arrivals`() {
        val f = StoreFixtures()
        val m = f.manager
        val fields = listOf(f.field("a"), f.field("b"), f.field("c"))
        val marks = listOf(f.mark("T"), f.mark("U"))
        fun paths(depth: Int): List<List<Int>> = if (depth == 0) listOf(emptyList()) else
            listOf(emptyList<Int>()) + paths(depth - 1).flatMap { tail -> fields.map { listOf(it) + tail } }
        val positions = paths(4).distinct()
        val choices = paths(2).distinct()
        fun denotation(values: List<TaintTree>, protected: Boolean): Set<Pair<List<Int>, TaintMark>> {
            val result = LinkedHashSet<Pair<List<Int>, TaintMark>>()
            for (value in values) {
                val source = if (protected) value.protectedPart() ?: continue else value
                for (leaf in f.ops.leaves(source)) for (path in positions) {
                    val prefix = leaf.fact.path
                    if (path.size < prefix.size || path.take(prefix.size) != prefix) continue
                    if (path.size > prefix.size && !leaf.exclusion.admits(path[prefix.size])) continue
                    result += path to (leaf.fact.mark as MarkSlot.Concrete).mark
                }
            }
            return result
        }
        for (seed in 0 until 8) {
            val random = Random(seed)
            val group = TaintGroup(m, m.newInterners().taint)
            val offered = ArrayList<TaintTree>()
            repeat(40) { step ->
                val excluded = ExclusionSet.of(fields.filter { random.nextBoolean() }.toIntArray())
                val selectedMarks = marks.filter { random.nextBoolean() }.ifEmpty { listOf(marks[0]) }
                var root: TaintNode? = null
                repeat(1 + random.nextInt(3)) {
                    val leaf = m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY,
                        MarkSet(selectedMarks.map { it.id }.toIntArray())))
                    val one = m.taintAlg.prepend(m, m.path(choices.random(random)), leaf)
                    root = root?.let { m.taintAlg.mergeAdd(it, one) } ?: one
                }
                val plain = m.taintTree(AccessPathBase.Argument(0), Layer.NORMAL, checkNotNull(root), excluded)
                val packet = if (random.nextInt(4) == 0) plain.withProtection(plain.root) else plain
                offered += packet
                group.addAll(packet)
                val current = group.all().toList()
                for (protected in listOf(false, true)) {
                    val expected = denotation(offered, protected)
                    val actual = denotation(current, protected)
                    assertTrue(expected == actual,
                        "seed=$seed step=$step protected=$protected missing=${expected - actual} extra=${actual - expected}; " +
                            "offers=" + offered.map { value ->
                                f.ops.leaves(value).toList() to value.protectedPart()?.let { f.ops.leaves(it).toList() }
                            })
                }
                assertTrue(group.addAll(packet).isEmpty(), "Repeated support must be idempotent")
            }
        }
    }
}
