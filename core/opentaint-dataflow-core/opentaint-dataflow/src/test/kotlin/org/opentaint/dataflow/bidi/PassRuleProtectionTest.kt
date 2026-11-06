package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.RunConfig
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.store.Record
import kotlin.test.*

class PassRuleProtectionTest {
    @Test fun `tagged pass actions never introduce protection in any application mode`() {
        for ((kind, role) in listOf(
            RuleKind.PASS_THROUGH to ActionRole.PASS_THROUGH,
            RuleKind.PASS_THROUGH to ActionRole.SOURCE,
            RuleKind.CALL_SOURCE to ActionRole.PASS_THROUGH,
        )) checkMicro(copyAll = false, protectedInput = false, kind = kind, role = role)
    }

    @Test fun `ordinary copy-all and copy-mark passes keep plain inputs plain`() {
        for (copyAll in listOf(false, true)) checkMicro(copyAll, protectedInput = false)
    }

    @Test fun `passes transport existing protection instead of clearing it`() {
        for (copyAll in listOf(false, true)) {
            checkMicro(copyAll, protectedInput = true)
            checkMicro(copyAll, protectedInput = true,
                kind = RuleKind.PASS_THROUGH, role = ActionRole.PASS_THROUGH)
        }
    }

    @Test fun `actual assignments retain the same-trigger protection rule`() {
        checkMicro(copyAll = false, protectedInput = false,
            kind = RuleKind.CALL_SOURCE, role = ActionRole.SOURCE, expectedProtected = true)
    }

    private fun checkMicro(copyAll: Boolean, protectedInput: Boolean,
                           kind: RuleKind? = null, role: ActionRole = ActionRole.PASS_THROUGH,
                           expectedProtected: Boolean = protectedInput) {
        for (mayTarget in listOf(false, true)) for (index in listOf(1, 2, 3)) for (markMode in
            if (index == 1) MarkMode.entries else listOf(MarkMode.FULL)) {
            MethodAnalysisFixtures().use { f ->
                val config = RunConfig(index, maxOf(1, index - 1),
                    if (index == 1) null else DemandStore.Builder(f.manager).build(),
                    f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = markMode)
                val core = f.core(config)
                val full = f.mark("T")
                val atom = MarkSlot.Concrete(f.manager.marks.runtimeAtom(full, config.mode.markMode))
                val fromPath = listOf(f.field("f"))
                val toPath = listOf(f.field("g"))
                val sideMark = if (copyAll) MarkSlot.STAR else MarkSlot.Concrete(full)
                val sideTail = if (copyAll) Tail.STAR else Tail.EXACT
                val forward = PathEdge(PathFact(AccessPathBase.Argument(0), fromPath, sideTail, sideMark),
                    PathFact(AccessPathBase.Return, toPath, if (mayTarget) Tail.ANY else sideTail, sideMark), ExclusionSet.Empty)
                val id = kind?.let { ActionId(RuleOccurrenceId(
                    FormKey(FormOwner(), f.key.method, f.key, f.inst(1)), it, 0), role, 0) }
                val transfer = MicroEdge(forward, forward, actionId = id)
                val directed = StatementSummary(setOf(forward.from.base, forward.to.base), listOf(transfer), emptyList(), emptyMap())
                    .let { if (config.direction == Direction.FORWARD) it else it.reversed() }
                val edge = directed.edges.single().edge
                val plain = f.fact(edge.from.base, edge.from.path, mark = atom) as TaintTree
                val input = if (protectedInput) plain.withProtection(plain.root) else plain
                val premise = f.manager.initial(f.pattern(edge.from.base, edge.from.path, mark = atom))
                for (application in MethodFormMode.entries) {
                    val output = applyMethodForm(core, application, directed, premise, input,
                        Place(f.inst(1), true, true)).map { it.second }
                    val label = "run-$index/$markMode/$application copyAll=$copyAll may=$mayTarget kind=$kind role=$role"
                    assertTrue(output.isNotEmpty(), label)
                    for (result in output) {
                        val taint = assertIs<TaintTree>(result, label)
                        assertEquals(edge.to.base, taint.base, label)
                        assertEquals(setOf(edge.to.path), f.ops.leaves(taint).map { it.fact.path }.toSet(), label)
                        val expectedTail = if (edge.to.tail == Tail.ANY) Tail.ANY else Tail.EXACT
                        assertTrue(f.ops.leaves(taint).all { it.fact.tail == expectedTail }, label)
                        val expectedLayer = if (mayTarget || config.mode.markMode == MarkMode.GROUP)
                            Layer.DEMAND else Layer.NORMAL
                        assertEquals(expectedLayer, taint.layer, label)
                        assertEquals(expectedProtected, taint.nonSubsumable != null, label)
                        if (expectedProtected) assertEquals(taint.root, taint.nonSubsumable, label)
                    }
                }
            }
        }
    }

    @Test fun `copy-all keeps plain sibling marks out of the protection mask`() {
        MethodAnalysisFixtures().use { f ->
            val core = f.core(index = 3)
            val t = MarkSlot.Concrete(f.mark("T"))
            val u = MarkSlot.Concrete(f.mark("U"))
            val a = AccessPathBase.Argument(0)
            val b = AccessPathBase.Return
            val protected = f.fact(a, mark = t) as TaintTree
            val plain = f.fact(a, mark = u) as TaintTree
            val payload = f.manager.taintAlg.mergeAdd(protected.root, plain.root, f.manager.cancellation)
            val input = f.manager.taintTree(a, Layer.NORMAL, payload, nonSubsumable = protected.root)
            val premise = f.manager.initial(f.pattern(a, tail = Tail.STAR, mark = MarkSlot.STAR))
            val stage = StatementSummary(setOf(a, b), listOf(MicroEdge.of(starEdge(a, emptyList(), b, emptyList()))),
                emptyList(), emptyMap())
            for (application in MethodFormMode.entries) {
                val output = applyMethodForm(core, application, stage, premise, input, Place(f.inst(1), true, true))
                    .single().second as TaintTree
                assertEquals(setOf(t, u), f.ops.leaves(output).map { it.fact.mark }.toSet())
                val flags = assertNotNull(output.protectedPart())
                assertEquals(setOf(t), f.ops.leaves(flags).map { it.fact.mark }.toSet())
            }
        }
    }

    @Test fun `mark-preserving and FLOW summaries transport flags without creating them`() {
        val f = StoreFixtures()
        val m = f.manager
        val mark = MarkSlot.Concrete(f.mark("T"))
        for (direction in Direction.entries) for (copyAll in listOf(false, true)) {
            val mode = ApMode(false, direction, 2)
            val tail = if (copyAll) Tail.STAR else Tail.EXACT
            val summaryMark = if (copyAll) MarkSlot.STAR else mark
            val initial = m.initial(f.pattern(AccessPathBase.Argument(0), tail = tail, mark = summaryMark))
            val conclusion = f.fact(AccessPathBase.Return, tail = tail, mark = summaryMark)
            for (summaryFlag in listOf(false, true)) {
                if (copyAll && summaryFlag) continue // A FLOW result has no concrete flag mask.
                val markedConclusion = if (summaryFlag) (conclusion as TaintTree).withProtection(conclusion.root) else conclusion
                val record = Record(f.method, direction, initial, markedConclusion)
                for (flagged in listOf(false, true)) {
                val plain = f.fact(AccessPathBase.Argument(0), mark = mark) as TaintTree
                val input = if (flagged) plain.withProtection(plain.root) else plain
                val original = m.initial(f.pattern(AccessPathBase.Argument(0), mark = mark))
                val out = CollectingOut()
                f.ops.applySummary(input, initial, markedConclusion, mode, out, original)
                assertTrue(out.results.isNotEmpty())
                for (result in out.results) assertEquals(flagged || summaryFlag, (result as TaintTree).nonSubsumable != null)

                val plainReverse = f.fact(AccessPathBase.Return, mark = mark) as TaintTree
                val reverseInput = if (flagged) plainReverse.withProtection(plainReverse.root) else plainReverse
                val reverseOriginal = m.initial(f.pattern(AccessPathBase.Return, mark = mark))
                var reads = 0
                record.forEachReversedAt(f.pattern(AccessPathBase.Return, mark = mark)) { view, protected ->
                    assertEquals(summaryFlag, protected)
                    val reversed = CollectingOut()
                    val opposite = if (direction == Direction.FORWARD) Direction.BACKWARD else Direction.FORWARD
                    f.ops.applyRecordLeaf(reverseInput, view, protected, ApMode(false, opposite, 2), reversed, reverseOriginal)
                    assertTrue(reversed.results.isNotEmpty())
                    for (result in reversed.results) assertEquals(flagged || summaryFlag, (result as TaintTree).nonSubsumable != null)
                    reads++
                }
                assertTrue(reads > 0)
                }
            }
        }
    }
}
