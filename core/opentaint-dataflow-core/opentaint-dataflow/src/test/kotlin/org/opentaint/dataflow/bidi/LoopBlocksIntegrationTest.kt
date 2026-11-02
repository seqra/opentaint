package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.bidi.store.BlockScope
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Physical operations run through the real driver. Helper projections alone
 * cannot satisfy these report, handoff, port and local-interface checks. */
class LoopBlocksIntegrationTest {
    private val a = AccessPathBase.LocalVar(0)
    private val b = AccessPathBase.LocalVar(1)
    private val returned = AccessPathBase.Return

    private fun observedCall(f: DriverFixtures, touched: Set<AccessPathBase>, transfer: StatementSummary,
                             sinks: List<SinkRule> = emptyList(), actions: List<CleanStep> = emptyList()): CallPlan {
        val identity = f.summary(ZERO_KEEP, *touched.map(::keepEdge).toTypedArray())
        val sourceStage = transfer.edges.any { it.isSource } || transfer.sources.isNotEmpty()
        return CallPlan(touched, listOf(
            CallStage.Edges(BEFORE, BOUND, BIND_IN, identity),
            CallStage.Actions(BOUND, ADDED, actions),
            CallStage.Edges(ADDED, RETURNED, if (sourceStage) SOURCES else UNRESOLVED, transfer),
            CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
            CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, identity),
        ), sinks, BEFORE, AFTER)
    }

    private fun getterCall(f: DriverFixtures, getter: MethodKey): CallPlan = CallPlan(setOf(STATIC, b), listOf(
        CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP, keepEdge(STATIC))),
        CallStage.Actions(BOUND, ADDED, emptyList()),
        CallStage.Callees(ADDED, RETURNED, listOf(getter)),
        CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
        CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP, keepEdge(STATIC),
            starEdge(returned, emptyList(), b, emptyList()))),
    ), emptyList(), BEFORE, AFTER)

    @Test fun `two successive loops retain scoped static guidance and resolve the later physical finding in FULL`() {
        DriverFixtures().use { f ->
            val p = f.program
            // main: prefix; while { a=sourceAtG(); C.shared=a; }
            //               while { b=get(); sinkT(b.g); } return;
            val root = p.method("two loop static root", listOf(
                listOf(1),           // 0 prefix
                listOf(2, 4),        // 1 L1 header: iterate or leave
                listOf(3),           // 2 source at a.g.$
                listOf(1),           // 3 real static write; repeat
                listOf(5, 7),        // 4 L2 header: iterate or leave
                listOf(6),           // 5 real getter call
                listOf(4),           // 6 physical sink; repeat
                listOf(8),           // 7 return transfer
                emptyList(),         // 8 normal boundary
                emptyList(),         // 9 exceptional boundary, unreachable forward
            ), normalExit = 8, exceptionalExit = 9, backwardExitDiscovery = true).key()
            val getter = p.method("two loop static getter", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val g = p.field("g")
            val cls = f.manager.accessors.index(ClassStaticAccessor("Box"))
            val field = p.field("shared")
            val slot = listOf(cls, field)
            val atom = p.mark("T")
            val mark = MarkSlot.Concrete(atom)
            val source = PathEdge(ZERO_FACT, PathFact(a, listOf(g), Tail.EXACT, mark), ExclusionSet.Empty)
            val sourcePlan = observedCall(f, setOf(a), f.summary(ZERO_KEEP, source))
            assertTrue(sourcePlan.stages.filterIsInstance<CallStage.Edges>().any { stage ->
                stage.kind == SOURCES && stage.summary.edges.any { it.forward === source }
            }, "The physical source must use SOURCES so its backward hit grants the next forward permission")
            p.call(root, 2, sourcePlan)
            val write = starEdge(a, emptyList(), STATIC, slot)
            p.staticWrite(root, 3, Pattern(write.to, ExclusionSet.Empty), write,
                f.summary(ZERO_KEEP, keepEdge(a), write))
            val read = starEdge(STATIC, slot, returned, emptyList())
            p.staticRead(getter, 1, read, f.summary(ZERO_KEEP, read))
            p.call(root, 5, getterCall(f, getter))
            val sink = SinkRule(f.rule("two loop static sink"), 0,
                listOf(p.pattern(b, listOf(g), mark = mark)), emptyList())
            p.call(root, 6, observedCall(f, setOf(b), f.summary(ZERO_KEEP, keepEdge(b)), listOf(sink)))

            val layout = f.shared.contexts.blockLayout(root)
            val composition1 = layout[layout.root]
            val loop1 = checkNotNull(composition1.loop)
            val after1 = layout[checkNotNull(composition1.after)]
            val loop2 = checkNotNull(after1.loop)
            assertEquals(composition1.after, layout[loop2].parent,
                "L2 belongs to the complete AL1 composition")
            assertTrue(layout[checkNotNull(after1.before)].instructions.isEmpty(), "BL2 is an empty logical block")
            assertEquals(loop1, layout.ownerOf(3))
            assertEquals(loop2, layout.ownerOf(6))

            val driver = f.driver(FixedLimits(listOf(1, 1, 2, 3, 4)), budget = 20.seconds,
                run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(root))
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertTrue(f.results.all { it.status == RunStatus.COMPLETE })
            assertTrue(f.results.flatMap { it.analyzers }.all { it.key in setOf(root, getter) },
                "Local blocks must not create generated public method identities")
            assertTrue(f.configs.all { it.mode.markMode == MarkMode.FULL })
            assertTrue(f.configs.any { it.index == 2 }, "The run-1 static candidate needs the backward handoff")
            assertEquals(0, driver.frontiers.first().reportedSinks, "Run-1 static approximation cannot settle this finding")
            assertTrue(report.end.run >= 3, "The finding must survive a real restricted backward run")
            val backwardRoot = f.results.single { it.runIndex == 2 }.analyzers.single { it.key == root }
            assertTrue(checkNotNull(backwardRoot.sourceHits).occurrences().any { hit ->
                hit.method == root && hit.statement == p.inst(root, 2) && hit.forward === source
            }, "The reverse source transfer must record the original physical source occurrence")
            assertTrue(f.configs.single { it.index == 3 }.seeds.allowsSource(root, p.inst(root, 2), source),
                "Run-3 must use the source permission produced by the real run-2 source callback")
            if (report.entries.none { it.descriptor.key.ruleId == sink.rule.id }) {
                println(buildString {
                    fun image(original: PremiseKey, value: Facts): String =
                        "${original.members.map { it.toPattern() }} -> ${f.ops.leaves(value).toList()} layer=${value.layer} protected=${(value as? TaintTree)?.nonSubsumable != null}"
                    fun terminal(row: TargetSummary): String = "${row.premise.members.map { it.toPattern() }} -> ${row.target}"
                    appendLine("TWO_LOOP_STATIC_TRACE end=${report.end}")
                    for (frontier in driver.frontiers) appendLine("frontier run=${frontier.run} demand=${frontier.demandEdges} targets=${frontier.targetDemand} reports=${frontier.reportedSinks}")
                    for (config in f.configs) appendLine("config run=${config.index} sourcePermission=${config.seeds.allowsSource(root, p.inst(root, 2), source)}")
                    for (result in f.results) for (actor in result.analyzers) {
                        appendLine("run=${result.runIndex} method=${actor.key.method.name} ROOT rows=${actor.summaries.all().map { image(it.first, it.second) }.toList()} targets=${actor.targets.map(::terminal)} sources=${actor.sourceHits?.entries()?.toList()}")
                        for (block in actor.blockSummaries()) appendLine("run=${result.runIndex} BLOCK key=${block.key} rows=${block.summaries.all().map { image(it.first, it.second) }.toList()}")
                        for (block in actor.blockTargets()) appendLine("run=${result.runIndex} TARGET scope=${block.scope} exit=${block.exit} rows=${block.rows.map(::terminal)}")
                    }
                    for (row in f.processed) appendLine("processed run=${row.run} method=${row.method.method.name} at=${row.delta.node.location.index} image=${image(row.delta.premise, row.delta.facts)}")
                })
            }
            assertEquals(listOf(sink.rule.id), report.entries.map { it.descriptor.key.ruleId },
                "end=${report.end}; frontiers=${driver.frontiers.map { Triple(it.run, it.demandEdges.values.sum(), it.reportedSinks) }}")
            assertEquals(p.inst(root, 6), report.entries.single().descriptor.key.statement)

            val first = f.results.first().analyzers.single { it.key == root }
            val localRows = first.blockSummaries().toList()
            assertTrue(localRows.isNotEmpty(), "The loop runtime must publish scoped snapshots, not use the flat method path")
            assertTrue(localRows.any { it.key.scope.block == loop1 }, "L1 has its own one-traversal rows")
            assertTrue(localRows.any { it.key.scope.block == loop2 }, "L2 has its own one-traversal rows")
            assertTrue(localRows.any { block -> block.summaries.all().any { it.second.base is AccessPathBase.LocalVar } },
                "Internal local conclusions must survive the public method summary-base filter")
            assertTrue(first.summaries.all().none { it.second.base is AccessPathBase.LocalVar })
            val outgoing = first.blockOutgoingTargets().filter { it.scope.block == loop2 }.toList()
            assertTrue(outgoing.any { block -> block.rows.any { it.target == Target.DemandTarget } },
                "The L2 sink has selected local terminal guidance")
            val backward = f.configs.single { it.index == 2 }
            val demand = checkNotNull(backward.demand)
            assertTrue(demand.hasSharedStaticCarry)
            assertTrue(demand.hasStaticCompletion)
            for (block in outgoing) {
                val reverseEntry = BlockScope(block.scope.block, block.exit)
                assertTrue(demand.scope(root, reverseEntry).initials(Reach.NORMAL, backward.admissionPolicy).isNotEmpty(),
                    "The opposite local entry retains its typed Target-to-ZERO permission")
            }
            assertTrue(f.processed.any { it.run == 2 && it.method == root &&
                it.delta.node in listOf(p.inst(root, 3), p.inst(root, 6)) },
                "Run-2 must visit the physical static write or consumer, not only a helper query")
            assertTrue(f.results.filter { it.direction == Direction.BACKWARD }.all { result ->
                result.analyzers.all { actor ->
                    actor.targets.none { it.target is Target.NormalTarget } &&
                        actor.blockTargets().flatMap { it.rows.asSequence() }.none { it.target is Target.NormalTarget }
                }
            })
        }
    }

    @Test fun `empty BL preserves repeat break throw and normal return ports without leaking a killed mark`() {
        DriverFixtures().use { f ->
            val p = f.program
            // x=sourceT(); while { repeat OR { clearAll(x); break; } OR throw; }
            // sinkClean(x); return x;   // Only the exceptional exit sink can report.
            val root = p.method("empty before loop exits", listOf(
                listOf(1, 2, 6),     // 0 header, also the method start
                listOf(0),           // 1 repeat
                listOf(3),           // 2 break through cleaner
                listOf(4),           // 3 clean normal-path sink
                listOf(5),           // 4 return transfer
                emptyList(),         // 5 normal boundary
                emptyList(),         // 6 exceptional boundary
            ), normalExit = 5, exceptionalExit = 6, backwardExitDiscovery = true).key()
            val mark = MarkSlot.Concrete(p.mark("T"))
            val source = PathEdge(ZERO_FACT, PathFact(a, emptyList(), Tail.EXACT, mark), ExclusionSet.Empty)
            p.entry(root, RuleStatement(f.summary(ZERO_KEEP, source), StatementSummary.EMPTY, emptyList()))
            val clean = CleanStep.Clean(Cleaner(a, null, CleanReach.AT_AND_BELOW, null))
            val identity = f.summary(ZERO_KEEP, keepEdge(a))
            p.call(root, 2, observedCall(f, setOf(a), identity, actions = listOf(clean)))
            val normalSink = SinkRule(f.rule("clean break sink"), 0, listOf(p.pattern(a, mark = mark)), emptyList())
            p.call(root, 3, observedCall(f, setOf(a), identity, listOf(normalSink)))
            p.statement(root, 4, f.summary(ZERO_KEEP, starEdge(a, emptyList(), returned, emptyList())))
            val thrownSink = SinkRule(f.rule("throw exit sink"), 0, listOf(p.pattern(a, mark = mark)), emptyList())
            p.exit(root, 6, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
                listOf(thrownSink)), false, emptySet()))
            val layout = f.shared.contexts.blockLayout(root)
            val top = layout[layout.root]
            assertTrue(layout[checkNotNull(top.before)].instructions.isEmpty())
            val loop = checkNotNull(top.loop)
            val repeat = checkNotNull(layout.port(1, 0)).id
            val breakPort = checkNotNull(layout.port(0, 2)).id
            val throwPort = checkNotNull(layout.port(0, 6)).id
            assertEquals(setOf(repeat), layout[loop].repeatPorts.toSet())

            val driver = f.driver(FixedLimits(listOf(1, 1, 2)), budget = 20.seconds, run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(root))
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertEquals(listOf(thrownSink.rule.id), report.entries.map { it.descriptor.key.ruleId })
            assertEquals(p.inst(root, 6), report.entries.single().descriptor.key.statement)
            val first = f.results.first().analyzers.single { it.key == root }
            val rows = first.blockSummaries().filter { it.key.scope.block == loop }.toList()
            assertTrue(rows.isNotEmpty(), "The original method actor must own actual loop snapshots")
            assertTrue(setOf(repeat, breakPort, throwPort).all { port -> rows.any { it.key.exit == port } },
                "Stored traversal rows keep separate repeat, break and exceptional ports")
            assertTrue(first.summaries.all().none { (_, facts) -> facts.base == returned &&
                f.ops.leaves(facts).any { it.fact.mark == mark } },
                "The thrown T path cannot create a normal return summary; the break path clears it")
            assertTrue(first.targets.none { row -> (row.target as? Target.NormalTarget)?.let {
                f.shared.reportCatalog.descriptor(it.id).key.ruleId == normalSink.rule.id
            } == true })
            assertTrue(first.blockTargets().flatMap { it.rows.asSequence() }.none { row ->
                (row.target as? Target.NormalTarget)?.let {
                    f.shared.reportCatalog.descriptor(it.id).key.ruleId == normalSink.rule.id
                } == true
            })
        }
    }
}
