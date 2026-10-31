package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import kotlin.test.*

/** FULL keeps exact evidence. GROUP projection, static routing, and AP loss keep their DEMAND rules. */
class Run1FullLayerPolicyTest {
    private val x = AccessPathBase.Argument(0)
    private val ret = AccessPathBase.Return
    private fun actor(f: MethodAnalysisFixtures, selected: MarkMode) = f.core(
        RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = selected))
    private fun address(f: MethodAnalysisFixtures, premise: PremiseKey, input: Facts) = OperationInput(
        ResumeSite.StatementInput(OperationId(FormKey(FormOwner(), f.key.method, f.key, f.inst(1)))), premise, input)

    @Test fun `FULL actor collectors preserve exact and MUST normal evidence and existing demand`() {
        for (tail in listOf(Tail.EXACT, Tail.ANY_TAINT, Tail.STAR, Tail.ANY))
            for (layer in Layer.entries) if (tail != Tail.ANY || layer == Layer.DEMAND)
                MethodAnalysisFixtures().use { f ->
                    val core = actor(f, MarkMode.FULL)
                    val value = f.fact(ret, tail = tail, layer = layer)
                    assertSame(value, core.forceRun1Layer(f.manager.zero, value))
                    val ordinary = ArrayList<Facts>()
                    core.collect(f.manager.zero, Reach.NORMAL) { _, result -> ordinary += result }.result(value)
                    assertEquals(listOf(value), ordinary, "tail=$tail layer=$layer")
                    val afterPolicy = ArrayList<Facts>()
                    core.collectAfterRun1Policy(address(f, f.manager.zero, Reach.NORMAL)) { _, result ->
                        afterPolicy += result
                    }.result(value)
                    assertEquals(listOf(value), afterPolicy, "The optimized collector has the same layer policy")
                }
    }

    @Test fun `ordinary nonzero FULL origins preserve their computed layer and GROUP concretions remain DEMAND`() {
        for (selected in MarkMode.entries) for (originTail in listOf(Tail.EXACT, Tail.STAR))
            for (tail in listOf(Tail.EXACT, Tail.ANY_TAINT, Tail.STAR, Tail.ANY))
                for (layer in Layer.entries) if (tail != Tail.ANY || layer == Layer.DEMAND)
                    MethodAnalysisFixtures().use { f ->
                        val core = actor(f, selected)
                        val origin = f.manager.initial(f.pattern(x, tail = originTail))
                        validateRun1Initial(origin, 1)
                        val raw = f.fact(ret, tail = tail, layer = layer)
                        val expected = if (selected == MarkMode.GROUP) Layer.DEMAND else layer
                        assertEquals(expected, core.forceRun1Layer(origin, raw).layer,
                            "mode=$selected origin=$originTail tail=$tail layer=$layer")
                        val ordinary = ArrayList<Facts>()
                        core.collect(origin, raw) { _, result -> ordinary += result }.result(raw)
                        assertEquals(listOf(expected), ordinary.map { it.layer })
                        val afterPolicy = ArrayList<Facts>()
                        core.collectAfterRun1Policy(address(f, origin, raw)) { _, result -> afterPolicy += result }
                            .result(f.ops.runtimeFact(raw, core.mode))
                        assertEquals(listOf(expected), afterPolicy.map { it.layer },
                            "The optimized callback must use the same ordinary layer policy")
                    }
    }

    @Test fun `GROUP still projects all concrete results to DEMAND while FULL source geometry decides its layer`() {
        for (selected in MarkMode.entries) MethodAnalysisFixtures().use { f ->
            val core = actor(f, selected)
            val t = f.mark("T")
            val mode = core.mode
            for (tail in listOf(Tail.EXACT, Tail.ANY_TAINT, Tail.ANY)) {
                val raw = PathEdge(ZERO_FACT, PathFact(ret, emptyList(), tail, MarkSlot.Concrete(t)), ExclusionSet.Empty)
                val outputs = ArrayList<Facts>()
                f.ops.applyEdge(Reach.NORMAL, f.manager.zero, raw, false, mode,
                    core.collect(f.manager.zero, Reach.NORMAL) { _, result -> outputs += result })
                val result = assertIs<TaintTree>(outputs.single())
                assertEquals(if (selected == MarkMode.GROUP || tail == Tail.ANY) Layer.DEMAND else Layer.NORMAL,
                    result.layer, "mode=$selected tail=$tail")
                assertEquals(MarkSlot.Concrete(f.manager.marks.runtimeAtom(t, selected)),
                    f.ops.leaves(result).single().fact.mark)
            }
        }
    }

    @Test fun `static results and static-origin images remain DEMAND in both mark modes`() {
        for (selected in MarkMode.entries) MethodAnalysisFixtures().use { f ->
            val core = actor(f, selected)
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val staticInitial = f.manager.initial(f.pattern(STATIC, path, Tail.STAR, MarkSlot.STAR))
            for (mark in listOf(MarkSlot.STAR, MarkSlot.Concrete(f.mark("T")))) {
                val tail = if (mark is MarkSlot.Star) Tail.STAR else Tail.EXACT
                val static = f.fact(STATIC, path, tail, mark)
                assertEquals(Layer.DEMAND, core.forceRun1Layer(f.manager.zero, static).layer)
                val image = f.fact(x, tail = tail, mark = mark)
                assertEquals(Layer.DEMAND, core.forceRun1Layer(staticInitial, image).layer)
                val after = ArrayList<Facts>()
                // This optimized callback receives an already projected AP result.
                core.collectAfterRun1Policy(address(f, staticInitial, image)) { _, result -> after += result }
                    .result(f.ops.runtimeFact(image, core.mode))
                assertEquals(Layer.DEMAND, after.single().layer)
            }
        }
    }

    @Test fun `FULL run1 cover keeps exact siblings NORMAL and demotes only E dependent tails`() =
        MethodAnalysisFixtures().use { f ->
            val core = actor(f, MarkMode.FULL)
            val t = f.mark("T")
            val u = f.mark("U")
            val root = f.manager.taintAlg.leafNode(f.manager.taintLeaves(MarkSet.of(t), MarkSet.of(u)))
            val raw = f.manager.taintTree(x, Layer.NORMAL, root, ExclusionSet.of(f.field("f")), Tail.ANY_TAINT)
            val outputs = ArrayList<Facts>()
            core.collect(f.manager.zero, Reach.NORMAL) { _, result -> outputs += result }.result(raw)
            val leaves = outputs.flatMap { value -> f.ops.leaves(value).map { it to value.layer }.toList() }.toSet()
            assertEquals(setOf(f.pattern(x, mark = MarkSlot.Concrete(t)) to Layer.NORMAL,
                f.pattern(x, tail = Tail.ANY_TAINT, mark = MarkSlot.Concrete(u)) to Layer.DEMAND), leaves)
            assertTrue(outputs.all { value -> f.ops.leaves(value).all { it.exclusion == ExclusionSet.Empty } })
        }

    @Test fun `FULL field overflow and exclusion needing overwrite remain DEMAND`() = MethodAnalysisFixtures().use { f ->
        val core = actor(f, MarkMode.FULL)
        val t = MarkSlot.Concrete(f.mark("T"))
        val field = f.field("f")
        val deep = f.fact(x, listOf(field, f.field("g")), Tail.EXACT, t)
        val cut = ArrayList<Facts>()
        core.cut(Cut.STATEMENT, f.manager.zero, deep) { _, value -> cut += value }
        assertEquals(Layer.DEMAND, cut.single().layer)
        assertEquals(Tail.ANY, f.ops.leaves(cut.single()).single().fact.tail)
        val input = f.fact(x, tail = Tail.ANY_TAINT, mark = t)
        val keep = keepEdge(x).copy(exclusion = ExclusionSet.of(field))
        val output = ArrayList<Facts>()
        f.ops.applyEdge(input, f.manager.zero, keep, true, core.mode,
            core.collect(f.manager.zero, input) { _, value -> output += value })
        assertEquals(Layer.DEMAND, output.single().layer)
        assertTrue(f.ops.leaves(output.single()).all { it.exclusion == ExclusionSet.Empty })
    }
}
