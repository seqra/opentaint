package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** The forward counterpart of the missing entry-inclusive prefix relation. */
class LoopBlockExitBoundaryFindingTest {
    private fun run(withLoop: Boolean) {
        DriverFixtures().use { f ->
            val p = f.program
            // Entry source: p and all descendants have T.
            // while (again()) { x.f=p; if (stop()) break; }
            // return x.f;
            // Normal exit rule: CM(ret.$,T).
            val method = p.method("exit boundary field write loop=$withLoop", listOf(
                listOf(1), listOf(2, 4), listOf(3),
                if (withLoop) listOf(1, 4) else listOf(4),
                listOf(5), emptyList(), emptyList()),
                normalExit = 5, exceptionalExit = 6, backwardExitDiscovery = true).key()
            val argument = AccessPathBase.Argument(0)
            val x = AccessPathBase.LocalVar(0)
            val returned = AccessPathBase.Return
            val field = p.field("f")
            val atom = p.mark("T")
            val mark = MarkSlot.Concrete(atom)
            val source = PathEdge(ZERO_FACT, PathFact(argument, emptyList(), Tail.ANY_TAINT, mark), ExclusionSet.Empty)
            p.entry(method, RuleStatement(f.summary(ZERO_KEEP, source), StatementSummary.EMPTY, emptyList()))
            p.statement(method, 2, MicroEdgeBuilder().apply {
                write(x, listOf(field), weak = false, values = listOf(argument), aliasPaths = emptyList())
            }.build())
            p.statement(method, 4, MicroEdgeBuilder().apply { read(returned, x, listOf(field)) }.build())
            val sink = SinkRule(f.rule("physical normal exit field sink"), 0,
                listOf(p.pattern(returned, mark = mark)), emptyList())
            p.exit(method, 5, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
                listOf(sink)), globalStateDrop = true, entryMarks = setOf(atom)))

            val driver = f.driver(FixedLimits(listOf(1, 1, 2, 3, 4)), 15.seconds,
                run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(method))
            if (report.entries.isEmpty()) println(buildString {
                appendLine("EXIT_BOUNDARY_TRACE loop=$withLoop end=${report.end}")
                for (config in f.configs) appendLine("config=${config.index} sourcePermission=${config.seeds.allowsSource(method, p.inst(method, 0), source)}")
                for (result in f.results) for (actor in result.analyzers) {
                    appendLine("run=${result.runIndex} ROOT targets=${actor.targets} sourceHits=${actor.sourceHits?.occurrences()?.toList()}")
                    for (block in actor.blockSummaries()) for ((origin, value) in block.summaries.all())
                        appendLine("run=${result.runIndex} key=${block.key} original=${origin.members.map { it.toPattern() }} value=${f.ops.leaves(value).toList()} layer=${value.layer}")
                    for (target in actor.blockTargets()) appendLine("run=${result.runIndex} TARGET=$target")
                    for (target in actor.blockOutgoingTargets()) appendLine("run=${result.runIndex} OUT_TARGET=$target")
                }
                for (row in f.processed) appendLine("run=${row.run} at=${row.delta.node.location.index} original=${row.delta.premise.members.map { it.toPattern() }} value=${f.ops.leaves(row.delta.facts).toList()} layer=${row.delta.facts.layer}")
            })
            assertEquals(RunStatus.COMPLETE, report.end.status)
            if (withLoop) {
                val layout = f.shared.contexts.blockLayout(method)
                val after = checkNotNull(layout[layout.root].after)
                val first = f.results.single { it.runIndex == 1 }.analyzers.single { it.key == method }
                val localTargets = first.blockOutgoingTargets().filter { it.scope.block == after }.toList()
                assertTrue(localTargets.any { block -> block.rows.any { row ->
                    row.target == Target.DemandTarget && row.premise.members.any {
                        it.base == x && it.mark == mark
                    }
                } }, "The actual normal-exit sink must first publish its AL-local marked dependency")
                assertTrue(first.outgoingTargets.any { it.premise.isZero && it.target == Target.DemandTarget },
                    "Ordinary parent composition must retain the enclosing method's true ZERO original")
                assertEquals(0, driver.frontiers.first().reportedSinks,
                    "The loop abstraction creates a real run-1 refinement candidate")
                assertTrue(f.configs.any { it.index == 3 }, "The finding needs the later forward replay")
                val backward = f.results.single { it.runIndex == 2 }.analyzers.single { it.key == method }
                val suffix = backward.blockSummaries().filter { it.key.scope.block == after }.flatMap { block ->
                    block.summaries.all().filter { (original, facts) ->
                        original.isZero && facts.layer == Layer.NORMAL && f.ops.leaves(facts).any {
                            it.fact.base == x && it.fact.path == listOf(field) &&
                                it.fact.tail == Tail.EXACT && it.fact.mark == mark
                        }
                    }.map { block.key }
                }.toList()
                assertTrue(suffix.isNotEmpty(),
                    "The exit-inclusive reverse AL must retain its genuine ZERO-origin suffix guidance")
                val forwardConfig = f.configs.single { it.index == 3 }
                val actual = f.manager.factsOf(PathFact(x, listOf(field), Tail.ANY_TAINT, mark),
                    ExclusionSet.Empty, Layer.NORMAL)
                assertTrue(suffix.any { producer ->
                    val reversed = producer.reversed()
                    checkNotNull(forwardConfig.demand).scope(method,
                        BlockScope(reversed.scope.block, reversed.scope.entry))
                        .initials(actual, forwardConfig.admissionPolicy).isNotEmpty()
                }, "The existing backward-ZERO exception must make the AL suffix a real forward consumer")
                val before = checkNotNull(layout[layout.root].before)
                assertTrue(first.blockSummaries().any { block ->
                    block.key.scope.block == before && block.key.scope.entry == PortId.ROOT_ENTRY &&
                        block.summaries.all().any { (original, facts) ->
                            original.isZero && facts.layer == Layer.NORMAL && f.ops.leaves(facts).any {
                                it.fact.base == argument && it.fact.path.isEmpty() &&
                                    it.fact.tail == Tail.ANY_TAINT && it.fact.mark == mark
                            }
                        }
                }, "The genuine NORMAL entry prefix can replay without another source hit or permission")
                val loop = layout.ownerOf(2)
                assertTrue(first.blockSummaries().any { block ->
                    block.key.scope.block == loop && block.summaries.all().any { (original, facts) ->
                        original.isFlow && original.members.any { it.base == argument && it.pathData.isEmpty() } &&
                            facts.layer == Layer.NORMAL && f.ops.leaves(facts).any {
                                it.fact.base == x && it.fact.path == listOf(field) &&
                                    it.fact.tail == Tail.STAR && it.fact.mark is MarkSlot.Star
                            }
                    }
                }, "The NORMAL cached loop write supplies the marked path without reprocessing physical write 2")
            } else assertEquals(1, report.end.run, "Removing only feedback makes the flat AP path NORMAL")
            assertEquals(listOf(sink.rule.id), report.entries.map { it.descriptor.key.ruleId }, "end=${report.end}")
            assertEquals(p.inst(method, 5), report.entries.single().descriptor.key.statement,
                "The sink is the real method exit rule, not a call in the following block")
        }
    }

    @Test fun `growing forward loop output reaches the real normal exit sink after saved after-region replay`() = run(true)
    @Test fun `same field write and real normal exit sink report when only feedback is removed`() = run(false)
}
