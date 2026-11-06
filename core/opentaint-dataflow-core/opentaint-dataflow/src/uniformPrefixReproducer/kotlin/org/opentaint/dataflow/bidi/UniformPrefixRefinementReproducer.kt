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
import java.nio.file.Path
import kotlin.time.Duration.Companion.seconds

/** Optional uniform-source refinement regression. Source p.f.ANY_TAINT/T
 * marks the whole subtree. The good mapper branch reads p.f.g; the broad branch
 * writes p to out.Element.h.extra. The sink observes exact T at mapped.Element.h.
 * Check compares the same field-limit checkpoint in both runtimes. Trace checks
 * eventual natural completion. This is a delay test, not a permanent-FN or
 * Conductor-cause claim. No summary, demand, initial or permission is injected.
 */
object UniformPrefixRefinementReproducer {
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
        val loaded = Path.of(Class.forName("org.opentaint.dataflow.bidi.ap.SpatialCanonicalKt")
            .protectionDomain.codeSource.location.toURI()).toRealPath()
        println("START mode=$mode SpatialCanonical=$loaded")
        println("POLICY_ORIGIN " + Class.forName("org.opentaint.dataflow.bidi.ap.RestrictedInitialPolicy")
            .protectionDomain.codeSource.location)
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
                p.pattern(input, listOf(f), Tail.ANY_TAINT, mark).fact, ExclusionSet.Empty)
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
            println("SOURCE $source; sink=mapped.Element.h.EXACT/T; methods=2")
            var processed = 0
            var firstNormalTarget: Int? = null
            val schedule = if (mode == "check") listOf(1, 1, 2) else listOf(1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10)
            println("CONFIG FULL heap=1g CPUs=1 budgetSeconds=20 limits=$schedule")
            val driver = fixture.driver(FixedLimits(schedule), 20.seconds, invokeRun = { config, shared, budget ->
                println("RUN_START ${config.index} ${config.direction} limit=${config.fieldLimit}")
                val result = fixture.run(config, shared, budget)
                // Current exports and actual onProcess rows, read before persist/handoff.
                for (actor in result.analyzers.filter { it.key == mapper })
                    for ((premise, value) in actor.summaries.all())
                        println("MAPPER_SUMMARY run=${config.index} P=${premise.members.map { it.toPattern() }} F=${facts(value)}")
                for (row in fixture.processed.drop(processed))
                    println("PROCESSED run=${config.index} method=${row.method} point=${row.delta.node.location.index} " +
                        "P=${row.delta.premise.members.map { it.toPattern() }} F=${facts(row.delta.facts)}")
                processed = fixture.processed.size
                for (actor in result.analyzers) for (target in actor.targets) {
                    println("TARGET run=${config.index} method=${actor.key} P=${target.premise.members.map { it.toPattern() }} ${target.target}")
                    if (actor.key == root && target.premise.isZero && target.target is Target.NormalTarget && firstNormalTarget == null)
                        firstNormalTarget = config.index
                }
                println("RUN_END ${config.index} ${result.status} limit=${config.fieldLimit}")
                result
            }, run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(root))
            for (frontier in driver.frontiers)
                println("FRONTIER run=${frontier.run} direction=${frontier.direction} demand=${frontier.demandEdges} " +
                    "targets=${frontier.targetDemand} reports=${frontier.reportedSinks}")
            val firstReport = driver.frontiers.firstOrNull { it.direction == Direction.FORWARD && it.reportedSinks > 0 }?.run
            val count = report.entries.count { it.descriptor.key.ruleId == sink.rule.id }
            println("RESULT mode=$mode firstNormalTarget=$firstNormalTarget firstReport=$firstReport " +
                "normalReports=$count terminal=${report.end}")
            println("QUALIFICATION processed rows have no BlockScope; no query or summary is injected")
            check(report.end.status == RunStatus.COMPLETE) { "Incomplete reproducer: ${report.end}" }
            if (mode == "check") {
                check(count == 1 && firstReport == 3) {
                    "Expected one NORMAL report by F3 for the uniform source; firstReport=$firstReport reports=$count. " +
                        "This checkpoint does not prove permanent finding loss; run trace."
                }
            } else {
                check(report.end.reason == EndReason.NO_DEMAND_EDGE) {
                    "Natural completion was not reached within the fixed schedule: ${report.end}. " +
                        "POLICY does not establish convergence."
                }
            }
        }
    }
}
