package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.RunStatus
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.time.Duration.Companion.seconds

/** A bounded refinement regression, not a permanent-FN or Conductor-specific proof.
 *
 * Code under analysis (f, g, h and extra are distinct fields):
 *   p.f.g = sourceT(); mapped = mapper(p); sinkT(mapped.Element.h);
 *   mapper(p) {
 *     if (flag) out.Element.h.extra = p;       // earlier predecessor, pc2
 *     else { part = p.f.g; out.Element.h = part; } // later predecessor, pc3/4
 *     return out;
 *   }
 *
 * Native reverse order visits the child arm first. At limit1, B2 can create
 * root+f MAY support under the same premise. Canonical prefix pruning removes
 * f; C2 then loses a deeper initial at F3. Check mode expects the finding by
 * F3. Trace mode shows whether later iterations recover it. Nothing is injected
 * into demand, record, initial, contributor or source-permission stores.
 */
object CanonicalPrefixRefinementReproducer {
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
        val mode = args.singleOrNull() ?: "check"
        require(mode == "check" || mode == "trace") { "Use check or trace" }
        println("MODE $mode; SpatialCanonical=" + Class.forName(
            "org.opentaint.dataflow.bidi.ap.SpatialCanonicalKt").protectionDomain.codeSource.location)
        DriverFixtures().use { fixture ->
            val p = fixture.program
            val f = p.field("f"); val g = p.field("g"); val h = p.field("h")
            val extra = p.field("extra")
            val element = fixture.manager.accessors.index(ElementAccessor)
            val mark = MarkSlot.Concrete(p.mark("T"))
            val root = p.method("canonical prefix root", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val mapper = p.method("canonical prefix mapper", listOf(
                listOf(1), listOf(2, 3), listOf(5), listOf(4), listOf(5), listOf(6), emptyList()), 6).key()
            val input = local(0); val mapped = local(1); val out = local(10); val part = local(11)
            val source = PathEdge(ZERO_FACT,
                p.pattern(input, listOf(f, g), Tail.EXACT, mark).fact, ExclusionSet.Empty)
            val occurrence = RuleOccurrenceId(FormKey(FormOwner(), root.method, root, p.inst(root, 0)),
                RuleKind.ENTRY_SOURCE, 0)
            val action = ActionId(occurrence, ActionRole.SOURCE, 0)
            p.entry(root, RuleStatement(MicroEdgeBuilder().apply {
                keepZero(); sourceEdge(source, action)
            }.build(), StatementSummary.EMPTY, emptyList()))
            p.call(root, 1, call(fixture, mapper, input, mapped))
            p.statement(mapper, 2, MicroEdgeBuilder().apply {
                write(out, listOf(element, h, extra), false, listOf(argument), emptyList())
            }.build())
            p.statement(mapper, 3, MicroEdgeBuilder().apply { read(part, argument, listOf(f, g)) }.build())
            p.statement(mapper, 4, MicroEdgeBuilder().apply {
                write(out, listOf(element, h), false, listOf(part), emptyList())
            }.build())
            p.statement(mapper, 5, MicroEdgeBuilder().apply { move(returned, out) }.build())
            val sink = SinkRule(fixture.rule("canonical prefix exact T"), 0,
                listOf(p.pattern(mapped, listOf(element, h), mark = mark)), emptyList())
            p.exit(root, 2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
                listOf(sink)), false, emptySet()))
            println("FIELDS f=$f g=$g h=$h extra=$extra Element=$element T=${mark.mark.id}")
            fun facts(value: Facts): String {
                val protected = (value as? TaintTree)?.protectedPart()?.let { fixture.ops.leaves(it).toList() }
                return "${value.layer} ${fixture.ops.leaves(value).toList()} protection=${protected.orEmpty()}"
            }
            var processed = 0
            var firstNormalTarget: Int? = null
            val limits: IterationPolicy = if (mode == "check") FixedLimits(listOf(1, 1, 2)) else IncreasingLimits
            val driver = fixture.driver(limits, 20.seconds, invokeRun = { config, shared, budget ->
                val result = fixture.run(config, shared, budget)
                // These are current admitted exports, read before persist/handoff.
                if (config.index == 2) for (actor in result.analyzers.filter { it.key == mapper })
                    for ((premise, value) in actor.summaries.all())
                        println("B2_SUMMARY P=${premise.members.map { it.toPattern() }} F=${facts(value)}")
                if (config.index == 3) for (row in fixture.processed.drop(processed))
                    if (row.method == mapper && row.delta.node.location.index == 0)
                        println("F3_EXECUTED_ENTRY P=${row.delta.premise.members.map { it.toPattern() }} " +
                            "F=${facts(row.delta.facts)} (onProcess does not supply BlockScope)")
                processed = fixture.processed.size
                for (actor in result.analyzers.filter { it.key == root }) for (target in actor.targets) {
                    println("RUN${config.index}_TARGET P=${target.premise.members.map { it.toPattern() }} ${target.target}")
                    if (target.premise.isZero && target.target is Target.NormalTarget && firstNormalTarget == null)
                        firstNormalTarget = config.index
                }
                println("RUN_END ${config.index} ${result.status} limit=${config.fieldLimit}")
                result
            }, run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(root))
            val firstReport = driver.frontiers.firstOrNull { it.direction == Direction.FORWARD && it.reportedSinks > 0 }?.run
            val count = report.entries.count { it.descriptor.key.ruleId == sink.rule.id }
            println("RESULT mode=$mode firstNormalTarget=$firstNormalTarget firstReport=$firstReport " +
                "normalReports=$count terminal=${report.end}")
            check(report.end.status == RunStatus.COMPLETE) { "Incomplete reproducer: ${report.end}" }
            if (mode == "check") check(count == 1 && firstReport == 3) {
                "Expected one NORMAL report by F3; firstReport=$firstReport reports=$count. " +
                    "This checkpoint failure does not prove a permanent false negative; run trace."
            }
        }
    }
}
