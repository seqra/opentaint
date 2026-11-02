package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
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

/** These are forward FULL controls. No backward ZERO/Target admission adapter is used. */
class LoopBlockCallsAndEntriesTest {
    private val x = AccessPathBase.LocalVar(0)
    private val y = AccessPathBase.LocalVar(1)
    private val z = AccessPathBase.LocalVar(2)

    private fun observed(f: DriverFixtures, positions: Set<AccessPathBase>,
                         source: PathEdge? = null, sinks: List<SinkRule> = emptyList()): CallPlan {
        val keep = f.summary(ZERO_KEEP, *positions.map(::keepEdge).toTypedArray())
        return CallPlan(positions, listOf(
            CallStage.Edges(BEFORE, BOUND, BIND_IN, keep),
            CallStage.Actions(BOUND, ADDED, emptyList()),
            CallStage.Edges(ADDED, RETURNED, if (source == null) UNRESOLVED else SOURCES,
                if (source == null) keep else f.summary(ZERO_KEEP, source)),
            CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
            CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, keep),
        ), sinks, BEFORE, AFTER)
    }

    @Test
    fun `irreducible loop keeps both physical entries and normal sink reports in run1`() {
        DriverFixtures().use { f ->
            val p = f.program
            // x=sourceT();
            // if (choose()) goto A; else goto B;
            // A: y=x; if (again()) goto B; else sinkT(y);
            // B: z=x; if (again()) goto A; else sinkT(z);
            // return;
            val root = p.method("multi entry loop", listOf(
                listOf(1),            // 0 entry
                listOf(2),            // 1 sourceT(x)
                listOf(3, 5),         // 2 two external entries into one SCC
                listOf(4),            // 3 header A: y=x
                listOf(5, 7),         // 4 repeat through B, or leave for sink(y)
                listOf(6),            // 5 header B: z=x
                listOf(3, 8),         // 6 repeat through A, or leave for sink(z)
                listOf(9),            // 7 sink(y)
                listOf(9),            // 8 sink(z)
                listOf(10),           // 9 return transfer
                emptyList(),          // 10 normal exit
                emptyList(),          // 11 exceptional exit, unreachable forward
            ), normalExit = 10, exceptionalExit = 11).key()
            val mark = MarkSlot.Concrete(p.mark("T"))
            val source = PathEdge(ZERO_FACT, PathFact(x, emptyList(), Tail.EXACT, mark), ExclusionSet.Empty)
            p.call(root, 1, observed(f, setOf(x), source))
            p.statement(root, 3, f.summary(ZERO_KEEP, keepEdge(x), starEdge(x, emptyList(), y, emptyList())))
            p.statement(root, 5, f.summary(ZERO_KEEP, keepEdge(x), starEdge(x, emptyList(), z, emptyList())))
            val sinkY = SinkRule(f.rule("multi entry y sink"), 0, listOf(p.pattern(y, mark = mark)), emptyList())
            val sinkZ = SinkRule(f.rule("multi entry z sink"), 0, listOf(p.pattern(z, mark = mark)), emptyList())
            p.call(root, 7, observed(f, setOf(y), sinks = listOf(sinkY)))
            p.call(root, 8, observed(f, setOf(z), sinks = listOf(sinkZ)))

            val layout = f.shared.contexts.blockLayout(root)
            val loop = layout.blocks.single { it.isLoop && it.headers.toSet() == setOf(3, 5) }
            val inputA = checkNotNull(layout.port(2, 3)).id
            val inputB = checkNotNull(layout.port(2, 5)).id
            val report = f.driver(FixedLimits(listOf(1)), 10.seconds,
                run1MarkMode = MarkMode.FULL).analyze(listOf(root))

            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertEquals(1, report.end.run)
            assertEquals(setOf(sinkY.rule.id, sinkZ.rule.id), report.entries.map { it.descriptor.key.ruleId }.toSet())
            assertEquals(2, report.entries.size)
            assertEquals(setOf(p.inst(root, 7), p.inst(root, 8)), report.entries.map { it.descriptor.key.statement }.toSet())
            assertEquals(setOf(root), f.results.single().analyzers.map { it.key }.toSet(),
                "Internal loop regions must not create new public method actors")
            val actor = f.results.single().analyzers.single()
            val entryPorts = actor.blockSummaries().filter { it.key.scope.block == loop.id }
                .map { it.key.scope.entry }.toSet()
            assertTrue(inputA in entryPorts && inputB in entryPorts,
                "Both original CFG entries must have their own instantiated loop scope: $entryPorts")
            for ((index, base) in listOf(7 to y, 8 to z)) assertTrue(f.processed.any { hit ->
                hit.run == 1 && hit.method == root && hit.delta.node == p.inst(root, index) &&
                    hit.delta.facts.base == base && hit.delta.facts.layer == Layer.NORMAL &&
                    f.ops.leaves(hit.delta.facts).any { it.fact.mark == mark }
            }, "A real NORMAL marked packet must reach physical sink $index")
            assertEquals(2, actor.targets.count { it.premise.isZero && it.target is Target.NormalTarget })
        }
    }

    @Test
    fun `real call in loop retains its local continuation and normal alias suffix`() {
        DriverFixtures().use { f ->
            val p = f.program
            val q = y
            val r = z
            val argument = AccessPathBase.Argument(0)
            val returned = AccessPathBase.Return
            // root: x=sourceT(); while (again()) { q=id(x); sinkT(aliasOf(q)); } return;
            val root = p.method("loop real caller", listOf(
                listOf(1),            // 0 entry
                listOf(2),            // 1 sourceT(x)
                listOf(3, 6),         // 2 loop header
                listOf(4),            // 3 q=id(x), r is an alias target of q
                listOf(5),            // 4 sinkT(r)
                listOf(2),            // 5 repeat
                listOf(7),            // 6 return transfer
                emptyList(),          // 7 normal exit
                emptyList(),          // 8 exceptional exit
            ), normalExit = 7, exceptionalExit = 8).key()
            // id(p): return p; The summary must be inferred from this real transfer.
            val callee = p.method("loop identity callee", listOf(listOf(1), listOf(2), emptyList()), normalExit = 2).key()
            p.statement(callee, 1, f.summary(ZERO_KEEP, keepEdge(argument),
                starEdge(argument, emptyList(), returned, emptyList())))
            val mark = MarkSlot.Concrete(p.mark("T"))
            val source = PathEdge(ZERO_FACT, PathFact(x, emptyList(), Tail.EXACT, mark), ExclusionSet.Empty)
            p.call(root, 1, observed(f, setOf(x), source))
            p.call(root, 3, CallPlan(setOf(x, q, r), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP,
                    starEdge(x, emptyList(), argument, emptyList()))),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Callees(ADDED, RETURNED, listOf(callee)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP,
                    starEdge(argument, emptyList(), x, emptyList()),
                    starEdge(returned, emptyList(), q, emptyList()))),
                CallStage.Edges(REWRITTEN, AFTER, ALIASES,
                    f.summary(starEdge(returned, emptyList(), r, emptyList())), Guard.MemoryEffect),
            ), emptyList(), BEFORE, AFTER))
            val sink = SinkRule(f.rule("loop real alias sink"), 0, listOf(p.pattern(r, mark = mark)), emptyList())
            p.call(root, 4, observed(f, setOf(r), sinks = listOf(sink)))

            val layout = f.shared.contexts.blockLayout(root)
            val loop = layout.ownerOf(3)
            assertTrue(layout[loop].isLoop)
            val report = f.driver(FixedLimits(listOf(1)), 10.seconds,
                run1MarkMode = MarkMode.FULL).analyze(listOf(root))

            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertEquals(1, report.end.run)
            assertEquals(listOf(sink.rule.id), report.entries.map { it.descriptor.key.ruleId })
            assertEquals(p.inst(root, 4), report.entries.single().descriptor.key.statement)
            assertEquals(setOf(root, callee), f.results.single().analyzers.map { it.key }.toSet())
            val allLinks = f.links(1, callee)
            val links = allLinks.filter { it.addedFact.fact.base != AccessPathBase.Zero }
            assertTrue(links.isNotEmpty(), "The original physical call must enter the real callee")
            assertTrue(allLinks.all { it.caller.call == p.inst(root, 3) && it.caller.scope != BlockScope.ROOT &&
                it.caller.scope.block == loop && it.caller.stageOrdinal == 2 })
            assertTrue(links.all { it.addedFact.fact.base == argument }, "Only BIND_IN's formal argument enters the callee")
            val calleeActor = f.results.single().analyzers.single { it.key == callee }
            assertTrue(calleeActor.summaries.all().any { (initial, facts) ->
                initial is InitialAp && initial.base == argument && initial.mark is MarkSlot.Star &&
                    facts is FlowTree && facts.base == returned && facts.layer == Layer.NORMAL
            }, "Infer the NORMAL argument-to-return FLOW row from the callee body")
            assertTrue(f.processed.any { hit -> hit.run == 1 && hit.method == root && hit.delta.node == p.inst(root, 4) &&
                hit.delta.facts.base == r && hit.delta.facts.layer == Layer.NORMAL &&
                f.ops.leaves(hit.delta.facts).any { it.fact.mark == mark } },
                "The guarded ALIASES suffix must deliver its marked physical fact to the in-loop sink")
            val caller = f.results.single().analyzers.single { it.key == root }
            val waitingScopes = links.map { it.caller.scope }.toSet()
            assertTrue(caller.blockSummaries().any { block -> block.key.scope in waitingScopes &&
                block.summaries.all().any { (_, facts) -> facts.base == r && facts.layer == Layer.NORMAL &&
                    f.ops.leaves(facts).any { it.fact.mark == mark } } },
                "The call result must resume and complete in its captured loop scope")
            assertTrue(caller.summaries.all().none { it.second.base in setOf(argument, r, q) },
                "Internal binding registers and locals must not become public method conclusions")
        }
    }
}
