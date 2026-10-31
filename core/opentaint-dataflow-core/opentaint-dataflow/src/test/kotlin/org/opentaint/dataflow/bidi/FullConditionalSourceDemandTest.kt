package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.bidi.store.DemandStore
import kotlin.test.*

/** Positive regression: an exact conditional source must survive a cut backward caller. No static state. */
class FullConditionalSourceDemandTest {
    @Test fun `FULL conditional source retains the good finding after a cut caller`() = DriverFixtures().use { f ->
        val p = f.program
        fun straight(size: Int) = List(size) { if (it + 1 < size) listOf(it + 1) else emptyList() }
        val root = p.method("conditional caller", straight(7), 6).key()
        val helper = p.method("conditional source", straight(2), 1).key()
        val a = AccessPathBase.LocalVar(0); val b = AccessPathBase.LocalVar(1)
        val r = AccessPathBase.LocalVar(2); val z = AccessPathBase.LocalVar(3)
        val y = AccessPathBase.LocalVar(4); val clean = AccessPathBase.LocalVar(5); val bad = AccessPathBase.LocalVar(6)
        val arg0 = AccessPathBase.Argument(0); val arg1 = AccessPathBase.Argument(1); val ret = AccessPathBase.Return
        val t1 = MarkSlot.Concrete(p.mark("T1")); val t2 = MarkSlot.Concrete(p.mark("T2"))
        val u = MarkSlot.Concrete(p.mark("U")); val field = p.field("f"); val g = p.field("g")
        val sa = PathEdge(ZERO_FACT, p.pattern(a, mark = t1).fact, ExclusionSet.Empty)
        val sb = PathEdge(ZERO_FACT, p.pattern(b, mark = t2).fact, ExclusionSet.Empty)
        p.entry(root, RuleStatement(f.summary(ZERO_KEEP, sa, sb), StatementSummary.EMPTY, emptyList()))
        val predicate = RulePredicate.Builder(f.cancellation).run {
            build(and(listOf(leaf(p.pattern(arg0, mark = t1)), leaf(p.pattern(arg1, mark = t2)))))
        }
        val occurrence = RuleOccurrenceId(FormKey(FormOwner(), helper.method, helper, helper.statement), RuleKind.CALL_SOURCE, 0)
        val action = SourceAction(ActionId(occurrence, ActionRole.SOURCE, 0), p.pattern(ret, mark = u).fact)
        p.statement(helper, 0, StatementSummary(setOf(arg0, arg1), listOf(MicroEdge.of(ZERO_KEEP)),
            emptyList(), emptyMap(), sources = listOf(SourceRuleOccurrence(occurrence, predicate, listOf(action)))))
        fun call(bindings: List<Pair<AccessPathBase, AccessPathBase>>, target: AccessPathBase) = CallPlan(
            bindings.map { it.first }.toSet() + target, listOf(
                CallStage.Edges(BEFORE, AFTER, PASS_OVER, f.summary(*bindings.map { keepEdge(it.first) }.toTypedArray())),
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP,
                    *bindings.map { starEdge(it.first, emptyList(), it.second, emptyList()) }.toTypedArray())),
                CallStage.Actions(BOUND, ADDED, emptyList()), CallStage.Callees(ADDED, RETURNED, listOf(helper)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP, starEdge(ret, emptyList(), target, emptyList()))),
            ), emptyList(), BEFORE, AFTER)
        p.call(root, 1, call(listOf(a to arg0, b to arg1), r))
        p.statement(root, 2, MicroEdgeBuilder().apply { write(z, listOf(g), false, listOf(r), emptyList()) }.build())
        p.statement(root, 3, MicroEdgeBuilder().apply { write(y, listOf(field), false, listOf(z), emptyList()) }.build())
        p.call(root, 5, call(listOf(a to arg0, clean to arg1), bad))
        val goodSink = SinkRule(f.rule("both inputs"), 0, listOf(p.pattern(y, listOf(field, g), mark = u)), emptyList())
        val badSink = SinkRule(f.rule("missing second input"), 0, listOf(p.pattern(bad, mark = u)), emptyList())
        p.exit(root, 6, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
            listOf(goodSink, badSink)), false, emptySet()))
        val report = f.driver(FixedLimits(listOf(1, 1, 2)), run1MarkMode = MarkMode.FULL).analyze(listOf(root))
        assertEquals(RunStatus.COMPLETE, report.end.status)
        val exact = p.pattern(ret, mark = u)
        val coarse = f.manager.factsOf(exact.fact.copy(tail = Tail.ANY), ExclusionSet.Empty, Layer.DEMAND)
        val exactControl = DemandStore.Builder(f.manager).apply {
            add(helper, DemandPattern(exact, ZERO_PATTERN))
        }.build()
        val policy = exactControl.admissionPolicy(2, 1, Direction.BACKWARD)
        assertEquals(setOf(AdmittedInitial(f.manager.initial(exact), Layer.DEMAND)),
            exactControl.initials(helper, coarse, policy),
            "The cut MAY offer supplies only an exact DEMAND hypothesis")
        val run1 = f.results.first().analyzers.single { it.key == helper }
        val exactOrigins = setOf(p.pattern(arg0, mark = t1), p.pattern(arg1, mark = t2))
        val starts = f.processed.filter { it.run == 1 && it.method == helper }.filter { row ->
            row.delta.premise.members.any { it.toPattern() in exactOrigins }
        }
        assertTrue(starts.isNotEmpty())
        val initialImages = starts.filter { it.delta.facts.base in setOf(arg0, arg1) }
        assertTrue(initialImages.isNotEmpty() && initialImages.all { it.delta.facts.layer == Layer.NORMAL },
            "Definite exact FULL request answers retain NORMAL")
        assertTrue(run1.summaries.all().none { (_, facts) -> facts.layer == Layer.NORMAL &&
            exact in f.ops.leaves(facts).toList() }, "A split arm cannot keep the other required input as an implicit NORMAL assumption")
        assertTrue(run1.summaries.demandEdges().any { (_, facts) -> exact in f.ops.leaves(facts).toList() },
            "The source waits for its full condition, then marks each weakened arm DEMAND")
        val nativeCandidates = f.records.byExit(helper, exact).toList()
        assertTrue(nativeCandidates.none { it.direction == Direction.FORWARD &&
            exact in f.ops.leaves(it.conclusion).toList() }, "A weakened arm is not a NORMAL native producer")
        val backwardStarts = f.processed.filter { it.run == 2 && it.method == helper &&
            it.delta.premise == f.manager.initial(exact) && it.delta.facts.base == ret &&
            exact in f.ops.leaves(it.delta.facts).toList() }.map { it.delta.facts.layer }.toSet()
        assertEquals(setOf(Layer.NORMAL, Layer.DEMAND), backwardStarts,
            "The good cut offer and bad exact sink requirement must process both admission lanes")
        val reportIds = report.entries.map { it.descriptor.key.ruleId }.toSet()
        println("FULL_CONDITIONAL_LAYER latest=run-${report.end.run} status=${report.end.status} reports=$reportIds")
        println("FULL_CONDITIONAL_LAYER runs=" + f.configs.map { it.index })
        println("FULL_CONDITIONAL_LAYER F1-helper-inputs=" + starts
            .map { row -> Triple(row.delta.premise.members.map { it.toPattern() },
                f.ops.leaves(row.delta.facts).toList(), row.delta.facts.layer) }.distinct())
        println("FULL_CONDITIONAL_LAYER F1-helper-summaries=" + run1.summaries.all().map { (origin, facts) ->
            Triple(origin.members.map { it.toPattern() }, f.ops.leaves(facts).toList(), facts.layer)
        }.toList())
        println("FULL_CONDITIONAL_LAYER native-candidates=" + nativeCandidates.map { record ->
            Triple(record.direction, record.premise.toPattern(), f.ops.leaves(record.conclusion).toList())
        })
        assertContains(reportIds, goodSink.rule.id,
            "The real two-input source flow must recover its full source permissions and later complete ND relation")
        assertFalse(badSink.rule.id in reportIds,
            "A caller without the second mark must remain negative; a complete condition is required at one caller")
    }
}
