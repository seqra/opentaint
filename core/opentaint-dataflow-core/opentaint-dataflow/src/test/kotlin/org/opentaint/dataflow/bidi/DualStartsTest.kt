package org.opentaint.dataflow.bidi

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.ap.ExclusionSet
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.starEdge
import kotlin.test.*

/** AP-level investigation. Does not install a new engine admission policy. */
class DualStartsTest {
    private val f = StoreFixtures()
    private val p = AccessPathBase.Argument(0)
    private val ret = AccessPathBase.Return
    private val g = f.field("g")
    private fun pat(base: AccessPathBase, tail: Tail, path: List<Int> = emptyList(), mark: MarkSlot = MarkSlot.STAR) =
        Pattern(PathFact(base, path, tail, mark), ExclusionSet.Empty)
    private fun packet(q: Pattern, layer: Layer) = f.manager.factsOf(q.fact, q.exclusion, layer)
    private fun collect(body: (ApOut) -> Unit): List<Facts> = ArrayList<Facts>().also { rows ->
        body(object : ApOut {
            override fun result(value: Facts) { rows += value }
            override fun markRequest(mark: TaintMark) = error("No mark requests in a restricted AP test")
        })
    }
    private fun apply(i: Pattern, layer: Layer, edge: PathEdge, direction: Direction): List<Facts> = collect { out ->
        f.ops.applyEdge(packet(i, layer), f.manager.initial(i), edge, true,
            ApMode(false, direction, 4), out)
    }
    private fun form(i: Pattern, result: Facts) = normalizeFlowSummary(f.manager, f.manager.initial(i), result)
    private fun view(rows: List<Facts>) = rows.flatMap { row ->
        f.ops.leaves(row).map { it to row.layer }.toList()
    }.toSet()

    @Test fun exactAndMayCopyStarts() {
        val move = starEdge(p, emptyList(), ret, emptyList())
        val exact = pat(p, Tail.EXACT)
        val may = pat(p, Tail.ANY)
        val normal = form(exact, apply(exact, Layer.NORMAL, move, Direction.FORWARD).single())
        val residual = form(may, apply(may, Layer.DEMAND, move, Direction.FORWARD).single())
        assertEquals(pat(p, Tail.STAR), normal.premise.members.single().toPattern())
        assertEquals(setOf(pat(ret, Tail.STAR) to Layer.NORMAL), view(listOf(normal.facts)))
        assertEquals(may, residual.premise.members.single().toPattern())
        assertEquals(setOf(pat(ret, Tail.ANY) to Layer.DEMAND), view(listOf(residual.facts)))
    }

    @Test fun sameHeadMayApplicationAgrees() {
        for (direction in Direction.entries) for (mark in listOf(MarkSlot.STAR, MarkSlot.Concrete(f.mark("T")))) {
            val actual = packet(pat(p, Tail.ANY, mark = mark), Layer.DEMAND)
            fun result(input: Tail, output: Tail, layer: Layer): List<Facts> = collect { out ->
                val key = f.manager.initial(pat(p, input))
                val selected = assertNotNull(f.ops.satisfying(actual, key, ApMode(false, direction, 4)))
                f.ops.applySummary(selected, key, packet(pat(ret, output), layer), ApMode(false, direction, 4), out)
            }
            val strong = result(Tail.STAR, Tail.STAR, Layer.NORMAL)
            val weak = result(Tail.ANY, Tail.ANY, Layer.DEMAND)
            assertEquals(view(strong), view(weak))
            assertEquals(setOf(pat(ret, Tail.ANY, mark = mark) to Layer.DEMAND), view(strong))
        }
    }

    @Test fun backwardGetterHasBothResults() {
        val read = starEdge(p, listOf(g), ret, emptyList())
        val backward = assertNotNull(f.ops.reverse(read))
        val exact = pat(ret, Tail.EXACT)
        val may = pat(ret, Tail.ANY)
        val normal = form(exact, apply(exact, Layer.NORMAL, backward, Direction.BACKWARD).single())
        val residual = form(may, apply(may, Layer.DEMAND, backward, Direction.BACKWARD).single())
        assertEquals(pat(ret, Tail.STAR), normal.premise.members.single().toPattern())
        assertEquals(setOf(pat(p, Tail.STAR, listOf(g)) to Layer.NORMAL), view(listOf(normal.facts)))
        assertEquals(may, residual.premise.members.single().toPattern())
        assertEquals(setOf(pat(p, Tail.ANY, listOf(g)) to Layer.DEMAND), view(listOf(residual.facts)))
    }

    @Test fun forwardGetterMustRetainMayWhenExactHasNoResult() {
        val read = starEdge(p, listOf(g), ret, emptyList())
        assertTrue(apply(pat(p, Tail.EXACT), Layer.NORMAL, read, Direction.FORWARD).isEmpty())
        val residual = apply(pat(p, Tail.ANY), Layer.DEMAND, read, Direction.FORWARD)
        assertEquals(setOf(pat(ret, Tail.ANY) to Layer.DEMAND), view(residual))
    }

    @Test fun descendantMayRequiresSeparateCoverageRule() {
        val t = MarkSlot.Concrete(f.mark("T"))
        val actual = packet(pat(p, Tail.ANY, listOf(g), t), Layer.DEMAND)
        fun result(input: Tail, output: Tail, layer: Layer) = collect { out ->
            val key = f.manager.initial(pat(p, input))
            val selected = assertNotNull(f.ops.satisfying(actual, key, ApMode(false, Direction.FORWARD, 4)))
            f.ops.applySummary(selected, key, packet(pat(ret, output), layer), ApMode(false, Direction.FORWARD, 4), out)
        }
        val strong = view(result(Tail.STAR, Tail.STAR, Layer.NORMAL))
        val weak = view(result(Tail.ANY, Tail.ANY, Layer.DEMAND))
        assertEquals(setOf(pat(ret, Tail.ANY, listOf(g), t) to Layer.DEMAND), strong)
        assertEquals(setOf(pat(ret, Tail.ANY, mark = t) to Layer.DEMAND), weak)
        assertNotEquals(strong, weak)
    }

    @Test fun concreteExactCompanionKeepsDemandAndDoesNotNormalize() {
        val t = MarkSlot.Concrete(f.mark("T"))
        val exact = pat(p, Tail.EXACT, mark = t)
        val actual = pat(p, Tail.ANY, mark = t)
        val policy = RestrictedInitialPolicy(3, 4, Direction.FORWARD, f.manager.marks)
        assertEquals(InitialEmission(exact, Layer.DEMAND), policy.emitAdmission(exact, actual, Layer.DEMAND))
        val image = packet(exact, Layer.DEMAND)
        val normalized = normalizeFlowSummary(f.manager, f.manager.initial(exact), image)
        assertEquals(exact, normalized.premise.members.single().toPattern())
        assertEquals(setOf(exact to Layer.DEMAND), view(listOf(normalized.facts)))
    }
}
