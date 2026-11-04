package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class LoopRestrictionSessionTest {
    @Test
    fun `finite native oracle verifies every skipped budget and every first accepted cut`() {
        val f = StoreFixtures()
        val x = AccessPathBase.Argument(0)
        val fields = listOf(f.field("f"), f.field("g"))
        val t = MarkSlot.Concrete(f.mark("T"))
        val paths = arrayListOf(emptyList<Int>())
        repeat(3) { depth -> paths += paths.filter { it.size == depth }.flatMap { p -> fields.map { p + it } } }
        val scope = BlockScope(BlockId(3), PortId(7))
        for (run in listOf(2, 3, 4)) {
            val policy = RestrictedInitialPolicy(run, 8, if (run % 2 == 0) Direction.BACKWARD else Direction.FORWARD, f.manager.marks)
            for (demandPath in paths) {
                val demands = listOf(f.pattern(x, demandPath, Tail.ANY, t),
                    f.pattern(x, demandPath.take(1), Tail.ANY, MarkSlot.STAR))
                val trie = FrozenDemandTrie.Builder<Pattern>(f.cancellation).apply { demands.forEach { add(it, it) } }.build()
                fun observe(value: Facts): LoopObservation<String> {
                    val initial = f.ops.leaves(value).flatMap { actual -> demands.mapNotNull { demand ->
                        policy.emitAdmission(demand, actual, value.layer)?.let { AdmittedInitial(f.manager.initial(it.pattern), it.layer) }
                    }.asSequence() }.toSet()
                    return LoopObservation(initial, listOf("enclosing witness"), emptyList(), initial.map {
                        LoopLabelledAdmission(scope, LoopAdmissionFamily.ADJACENT, it)
                    })
                }
                val session = LoopRestrictionSession(f.ops, policy, ::observe) { actual ->
                    trie.precisionCursors(actual, f.manager.marks).map {
                        LoopPrecisionCursor(scope, LoopAdmissionFamily.ADJACENT, it)
                    }
                }
                for (rawPath in paths.filter { it.size >= 2 }) for (tail in listOf(Tail.EXACT, Tail.ANY, Tail.STAR, Tail.ANY_TAINT)) {
                    val raw = f.fact(x, rawPath, tail, t, layer = if (tail == Tail.ANY) Layer.DEMAND else Layer.NORMAL)
                    val baseline = observe(raw)
                    val first = session.certifiedFirstBudget(raw, baseline)
                    if (first != null) for (budget in 1 until first) {
                        val out = CollectingOut(); f.ops.limit(raw, budget, out)
                        assertNotEquals(baseline, observe(out.results.single()), "run-$run $demandPath $rawPath $tail budget=$budget")
                    }
                    assertEquals(LoopOutputRestriction(f.ops).restrict(false, true, raw, ::observe),
                        LoopOutputRestriction(f.ops).restrict(false, true, raw, session))
                }
            }
        }
    }

    @Test
    fun `certificate rejects earlier cuts but keeps native first result and complete observations`() {
        val f = StoreFixtures()
        val x = AccessPathBase.Argument(0)
        val path = listOf(f.field("f"), f.field("g"), f.field("h"), f.field("k"))
        val t = MarkSlot.Concrete(f.mark("T"))
        val demands = listOf(f.pattern(x, path.take(1), Tail.ANY, t), f.pattern(x, path.take(2), Tail.ANY, t))
        val trie = FrozenDemandTrie.Builder<Pattern>(f.cancellation).apply { demands.forEach { add(it, it) } }.build()
        val scope = BlockScope(BlockId(1), PortId(2))
        val policy = RestrictedInitialPolicy(3, 8, Direction.FORWARD, f.manager.marks)
        fun observe(value: Facts): LoopObservation<String> {
            val initial = f.ops.leaves(value).flatMap { actual -> demands.mapNotNull { demand ->
                policy.emitAdmission(demand, actual, value.layer)?.let { AdmittedInitial(f.manager.initial(it.pattern), it.layer) }
            }.asSequence() }.toSet()
            return LoopObservation(initial, listOf("complete enclosing result"), emptyList(), initial.map {
                LoopLabelledAdmission(scope, LoopAdmissionFamily.ADJACENT, it)
            })
        }
        val raw = f.fact(x, path, mark = t)
        val session = LoopRestrictionSession(f.ops, policy, ::observe) { actual ->
            trie.precisionCursors(actual, f.manager.marks).map { LoopPrecisionCursor(scope, LoopAdmissionFamily.ADJACENT, it) }
        }
        assertEquals(3, session.certifiedFirstBudget(raw, observe(raw)))
        val reference = LoopOutputRestriction(f.ops)
        val optimized = LoopOutputRestriction(f.ops)
        val expected = reference.restrict(false, true, raw, ::observe)
        assertEquals(expected, optimized.restrict(false, true, raw, session))
        assertEquals(3L, reference.statistics.trials)
        assertEquals(1L, optimized.statistics.trials)
        assertEquals(2L, optimized.statistics.budgetsSkipped)
    }

    @Test
    fun `a witness already in the baseline cannot skip an earlier valid cut`() {
        val f = StoreFixtures()
        val x = AccessPathBase.Argument(0)
        val path = listOf(f.field("f"), f.field("g"))
        val t = MarkSlot.Concrete(f.mark("T"))
        val demand = f.pattern(x, path, Tail.ANY, t)
        val trie = FrozenDemandTrie.Builder<Pattern>(f.cancellation).apply { add(demand, demand) }.build()
        val scope = BlockScope(BlockId(1), PortId(2))
        val policy = RestrictedInitialPolicy(3, 8, Direction.FORWARD, f.manager.marks)
        fun observe(value: Facts): LoopObservation<String> {
            val emitted = policy.emitAdmission(demand, f.ops.leaves(value).single(), value.layer)!!
            val admitted = AdmittedInitial(f.manager.initial(emitted.pattern), emitted.layer)
            return LoopObservation(listOf(admitted), emptyList(), emptyList(),
                listOf(LoopLabelledAdmission(scope, LoopAdmissionFamily.REPEAT, admitted)))
        }
        val raw = f.fact(x, path, Tail.ANY, t, layer = Layer.DEMAND)
        val session = LoopRestrictionSession(f.ops, policy, ::observe) { actual ->
            trie.precisionCursors(actual, f.manager.marks).map { LoopPrecisionCursor(scope, LoopAdmissionFamily.REPEAT, it) }
        }
        assertNull(session.certifiedFirstBudget(raw, observe(raw)))
        val optimized = LoopOutputRestriction(f.ops)
        val kept = optimized.restrict(false, true, raw, session).single()
        assertEquals(path.take(1), f.ops.leaves(kept).single().fact.path)
        assertEquals(1L, optimized.statistics.trials)
    }
}
