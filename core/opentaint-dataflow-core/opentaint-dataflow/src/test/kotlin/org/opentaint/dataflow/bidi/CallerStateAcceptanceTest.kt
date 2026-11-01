package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.engine.Target

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.Seed
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.driver.ReportBuilder
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.bidi.store.DemandStore
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Analyzer inventory 18/interpreter 23: caller-owned state is not callee-owned G2 state. */
class CallerStateAcceptanceTest {
    @Test
    fun `caller state triggers release and remains visible after its G2 exit in a FULL run`(): Unit {
        DriverFixtures().use { f ->
            val root = f.program.method("caller state root", listOf(listOf(1), listOf(2), listOf(3), listOf(4), emptyList()), 4).key()
            val acquire = f.program.method("acquire state", listOf(listOf(1), emptyList()), 1).key()
            val release = f.program.method("release state", listOf(listOf(1), emptyList()), 1).key()
            val after = f.program.method("after state", listOf(listOf(1), emptyList()), 1).key()
            val static = AccessPathBase.ClassStatic
            val cls = f.manager.accessors.index(ClassStaticAccessor("Lock"))
            val mark = MarkSlot.Concrete(f.program.mark("STATE"))
            val state = f.program.pattern(static, listOf(cls), Tail.EXACT, mark)
            val source = PathEdge(ZERO_FACT, state.fact, ExclusionSet.Empty)
            f.program.entry(acquire, RuleStatement(f.summary(ZERO_KEEP, source), StatementSummary.EMPTY, emptyList()))
            val taint = MarkSlot.Concrete(f.program.mark("T"))
            val returned = f.program.pattern(AccessPathBase.Return, mark = taint)
            val releaseResult = PathEdge(ZERO_FACT, returned.fact, ExclusionSet.Empty)
            val afterResult = PathEdge(ZERO_FACT, returned.fact, ExclusionSet.Empty)
            f.program.entry(release, RuleStatement(f.summary(ZERO_KEEP, releaseResult), StatementSummary.EMPTY, emptyList()))
            f.program.entry(after, RuleStatement(f.summary(ZERO_KEEP, afterResult), StatementSummary.EMPTY, emptyList()))
            val releaseSink = SinkRule(f.rule("release state sink"), 0, listOf(state, returned), emptyList())
            val afterSink = SinkRule(f.rule("after state sink"), 0, listOf(state, returned), emptyList())
            fun exit(sink: SinkRule): ExitRules = ExitRules(
                RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, listOf(sink)), true, emptySet())
            f.program.exit(release, 1, exit(releaseSink))
            f.program.exit(after, 1, exit(afterSink))
            fun call(callee: MethodKey): CallPlan {
                // Consume the caller's Result at each binding. Each callee generates its own tainted Result.
                val identity = StatementSummary(setOf(static, AccessPathBase.Zero, AccessPathBase.Return),
                    listOf(MicroEdge.of(keepEdge(static)), MicroEdge.of(ZERO_KEEP)), emptyList(), emptyMap())
                return CallPlan(setOf(static, AccessPathBase.Zero, AccessPathBase.Return), listOf(
                    CallStage.Edges(BEFORE, BOUND, BIND_IN, identity),
                    CallStage.Actions(BOUND, ADDED, emptyList()),
                    CallStage.Callees(ADDED, RETURNED, listOf(callee)),
                    CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                    CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, identity),
                ), emptyList(), BEFORE, AFTER)
            }
            f.program.call(root, 1, call(acquire))
            f.program.call(root, 2, call(release))
            f.program.call(root, 3, call(after))

            val demand = DemandStore.Builder(f.manager).also { builder ->
                for (method in listOf(root, acquire, release, after))
                    builder.add(method, DemandPattern(ZERO_PATTERN, ZERO_PATTERN))
                builder.add(acquire, DemandPattern(f.manager.zero.toPattern(), state))
                builder.add(release, DemandPattern(state, state))
                builder.add(after, DemandPattern(state, state))
                // These independent ZERO sources have explicit summary exit permission.
                builder.add(release, DemandPattern(ZERO_PATTERN, returned))
                builder.add(after, DemandPattern(ZERO_PATTERN, returned))
            }.build()
            // Run-1 has no class-root initials or static call-chain relays.
            // GroupedStaticPipelineTest covers its operation-local pool path.
            for (index in listOf(3)) {
                val config = RunConfig(index, 2,
                    if (index == 1) null else demand, f.records.view(),
                    if (index == 1) SeedIndex.EMPTY else SeedIndex.of(listOf(
                        Seed.Source(acquire, f.program.inst(acquire, 0), source),
                        Seed.Source(release, f.program.inst(release, 0), releaseResult),
                        Seed.Source(after, f.program.inst(after, 0), afterResult))),
                    listOf(root))
                val result = f.run(config, timeout = 5.seconds)
                assertEquals(RunStatus.COMPLETE, result.status)
                assertTrue(f.records.byEntry(release, state).none(), "No previous-run record may mask state loss at release")
                val actors = result.analyzers.associateBy { it.key }
                val initial = f.manager.initial(state)
                val expected = Conclusion(state.fact, ExclusionSet.Empty, false)
                for (callee in listOf(release, after)) {
                    val actor = actors.getValue(callee)
                    assertTrue(actor.summaries.all().any { (premise, facts) ->
                        premise == initial && f.ops.leaves(facts).any {
                            Conclusion(it.fact, it.exclusion, facts.layer == Layer.DEMAND) == expected
                        }
                    }, "Caller-owned state must remain in $callee's nonzero admitted summary in run $index")
                    val link = f.links(index, actor.key).asSequence().single { it.addedFact == state && it.caller.caller == root }
                    assertEquals(Layer.NORMAL, link.linkLayer)
                    assertEquals(Layer.NORMAL, link.caller.callerLayer)
                    assertTrue(link.caller.premise.isZero)
                    assertEquals(f.program.inst(root, if (callee == release) 2 else 3), link.caller.call)
                    assertTrue(actor.summaries.all().any { (premise, facts) ->
                        premise.isZero && facts.layer == Layer.NORMAL && f.ops.leaves(facts).any { it.fact == returned.fact }
                    }, "Each callee's zero source supplies its independent Result literal")
                }
                for ((callee, sink) in listOf(release to releaseSink, after to afterSink)) {
                    val terminal = actors.getValue(callee).targets.single()
                    assertSame(initial, terminal.premise)
                    val id = assertIs<Target.NormalTarget>(terminal.target).id
                    assertEquals(SinkKey(callee.method, f.program.inst(callee, 1), sink.rule.id),
                        f.shared.reportCatalog.descriptor(id).key)
                }
                val report = ReportBuilder().also { it.commit(it.prepare(config, result, f.shared)) }
                    .build(org.opentaint.dataflow.bidi.driver.AnalysisEnd(RunStatus.COMPLETE,
                        index, Direction.FORWARD, org.opentaint.dataflow.bidi.driver.EndReason.POLICY))
                assertEquals(setOf(releaseSink.rule.id, afterSink.rule.id),
                    report.entries.map { it.descriptor.key.ruleId }.toSet())
                if (index == 3) {
                    assertTrue(actors.getValue(release).summaries.demandEdges(Direction.FORWARD).none())
                    assertTrue(actors.getValue(after).summaries.demandEdges(Direction.FORWARD).none())
                }
            }
        }
    }
}
