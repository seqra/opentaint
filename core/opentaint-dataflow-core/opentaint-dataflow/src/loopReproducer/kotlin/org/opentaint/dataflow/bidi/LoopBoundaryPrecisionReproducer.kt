package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.RunStatus
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.time.Duration.Companion.seconds

/** A converged coverage regression with one marker and a direct observation.
 *
 * Code under analysis:
 *   s = sourceT();
 *   do { temp.g = s; next.f = temp; s = next; } while (again);
 *   mapped = mapper(s); sinkT(mapped.Element.h);
 *   mapper(q) {
 *     if (flag) out.Element.h = getG(getF(q));
 *     else      out.Element.h = q;
 *     return out;
 *   }
 *
 * The loop runs at least once. On its first exit, s.f.g is the original
 * source object. The getter branch therefore supplies exact T at Element.h.
 * The check waits for natural driver convergence and expects a NORMAL report.
 * It supplies no demand, saved record, initial, contributor or source permission.
 * This case does not isolate canonical prefix pruning as the cause.
 */
object LoopBoundaryPrecisionReproducer {
    private val argument = AccessPathBase.Argument(0)
    private val returned = AccessPathBase.Return
    private fun local(index: Int) = AccessPathBase.LocalVar(index)

    private fun call(f: DriverFixtures, callee: MethodKey, input: AccessPathBase,
                     output: AccessPathBase) = CallPlan(setOf(input, output), listOf(
        CallStage.Edges(BEFORE, AFTER, PASS_OVER, f.summary(keepEdge(input))),
        CallStage.Edges(BEFORE, BOUND, BIND_IN,
            f.summary(ZERO_KEEP, starEdge(input, emptyList(), argument, emptyList()))),
        CallStage.Actions(BOUND, ADDED, emptyList()),
        CallStage.Callees(ADDED, RETURNED, listOf(callee)),
        CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
        CallStage.Edges(REWRITTEN, AFTER, BIND_BACK,
            f.summary(ZERO_KEEP, starEdge(returned, emptyList(), output, emptyList()))),
    ), emptyList(), BEFORE, AFTER)

    @JvmStatic fun main(args: Array<String>) {
        require(args.isEmpty()) { "This check runs through natural convergence; no mode arguments" }
        println("SpatialCanonical=" + Class.forName(
            "org.opentaint.dataflow.bidi.ap.SpatialCanonicalKt").protectionDomain.codeSource.location)
        DriverFixtures().use { fixture ->
            val p = fixture.program
            val f = p.field("f"); val g = p.field("g"); val h = p.field("h")
            val element = fixture.manager.accessors.index(ElementAccessor)
            val mark = MarkSlot.Concrete(p.mark("T"))
            val root = p.method("Loop direct T observer root", listOf(
                listOf(1), listOf(2), listOf(3), listOf(4), listOf(1, 5), listOf(6), emptyList()), 6).key()
            val mapper = p.method("Loop direct T branch mapper", listOf(
                listOf(1), listOf(2, 5), listOf(3), listOf(4), listOf(8),
                listOf(6), listOf(7), listOf(8), listOf(9), emptyList()), 9).key()
            val getF = p.method("Loop direct T getter f", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val getG = p.method("Loop direct T getter g", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val s = local(0); val mapped = local(1); val temp = local(6); val next = local(7)
            val out = local(10); val gotF = local(11); val gotG = local(12)
            val root1 = local(20); val root2 = local(21)
            val source = PathEdge(ZERO_FACT, p.pattern(s, mark = mark).fact, ExclusionSet.Empty)
            val occurrence = RuleOccurrenceId(FormKey(FormOwner(), root.method, root, p.inst(root, 0)),
                RuleKind.ENTRY_SOURCE, 0)
            val action = ActionId(occurrence, ActionRole.SOURCE, 0)
            p.entry(root, RuleStatement(MicroEdgeBuilder().apply {
                keepZero(); sourceEdge(source, action)
            }.build(), StatementSummary.EMPTY, emptyList()))
            p.statement(root, 1, MicroEdgeBuilder().apply { write(temp, listOf(g), false, listOf(s), emptyList()) }.build())
            p.statement(root, 2, MicroEdgeBuilder().apply { write(next, listOf(f), false, listOf(temp), emptyList()) }.build())
            p.statement(root, 3, MicroEdgeBuilder().apply { move(s, next) }.build())
            p.call(root, 5, call(fixture, mapper, s, mapped))
            p.call(mapper, 2, call(fixture, getF, argument, gotF))
            p.call(mapper, 3, call(fixture, getG, gotF, gotG))
            p.statement(mapper, 4, MicroEdgeBuilder().apply {
                write(out, listOf(element, h), false, listOf(gotG), emptyList())
            }.build())
            // Keep the two ordinary copies on the broad branch from the reduced case.
            p.statement(mapper, 5, MicroEdgeBuilder().apply { move(root1, argument) }.build())
            p.statement(mapper, 6, MicroEdgeBuilder().apply { move(root2, root1) }.build())
            p.statement(mapper, 7, MicroEdgeBuilder().apply {
                write(out, listOf(element, h), false, listOf(root2), emptyList())
            }.build())
            p.statement(mapper, 8, MicroEdgeBuilder().apply { move(returned, out) }.build())
            p.statement(getF, 1, MicroEdgeBuilder().apply { read(returned, argument, listOf(f)) }.build())
            p.statement(getG, 1, MicroEdgeBuilder().apply { read(returned, argument, listOf(g)) }.build())
            val sink = SinkRule(fixture.rule("Loop direct T Element.h observation"), 0,
                listOf(p.pattern(mapped, listOf(element, h), mark = mark)), emptyList())
            p.exit(root, 6, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
                listOf(sink)), false, emptySet()))
            println("FIELDS f=$f g=$g h=$h Element=$element T=${mark.mark.id}")
            val driver = fixture.driver(FixedLimits(listOf(1, 1, 2, 3, 4, 5, 6, 7, 8, 9)), 20.seconds,
                invokeRun = { config, shared, budget ->
                    fixture.run(config, shared, budget).also { result ->
                        println("RUN_END ${config.index} ${result.status} limit=${config.fieldLimit}")
                    }
                }, run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(root))
            val count = report.entries.count { it.descriptor.key.ruleId == sink.rule.id }
            val firstReport = driver.frontiers.firstOrNull {
                it.direction == Direction.FORWARD && it.reportedSinks > 0
            }?.run
            println("RESULT firstReport=$firstReport normalReports=$count terminal=${report.end}")
            check(report.end.status == RunStatus.COMPLETE && report.end.reason == EndReason.NO_DEMAND_EDGE) {
                "Expected natural convergence: ${report.end}"
            }
            check(count == 1) {
                "Expected one NORMAL report for sourceT -> s.f.g -> mapped.Element.h after convergence; " +
                    "got $count at run ${report.end.run}."
            }
        }
    }
}
