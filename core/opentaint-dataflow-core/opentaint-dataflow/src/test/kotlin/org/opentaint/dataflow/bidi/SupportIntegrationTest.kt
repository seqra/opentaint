package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.engine.Target

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.Seed
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.fixtures.HistoricalSupport
import org.opentaint.dataflow.bidi.fixtures.HistoricalSupportInput
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.FiniteProgramFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.bidi.store.CallerRef
import org.opentaint.dataflow.bidi.store.Link
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import java.util.concurrent.ConcurrentLinkedQueue
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Joined terminal summaries retain complete premises without callee input history. */
class SupportIntegrationTest {
    private val x = AccessPathBase.Argument(0)
    private val y = AccessPathBase.Argument(1)
    private val inputs = ConcurrentLinkedQueue<Pair<MethodKey, Link>>()
    private fun links(key: MethodKey): Set<Link> = inputs.filter { it.first == key }.map { it.second }.toSet()
    private fun historical(result: RunResult<RunMethodAnalyzer>, config: RunConfig, f: FiniteProgramFixtures) =
        HistoricalSupport(HistoricalSupportInput(result, inputs.groupBy({ it.first }, { it.second })),
            config.roots, config.mode, f.shared)
    private fun candidateReport(config: RunConfig, result: RunResult<RunMethodAnalyzer>, f: FiniteProgramFixtures) {
        val builder = ReportBuilder()
        builder.commit(builder.prepare(config, result, f.shared))
        val report = builder.build(AnalysisEnd(RunStatus.COMPLETE, config.index, config.direction, EndReason.POLICY))
        val expected = result.analyzers.filter { it.key in config.roots }.flatMap { actor ->
            actor.targets.mapNotNull { row ->
                (row.target as? Target.NormalTarget)?.id?.takeIf { row.premise.isZero }
            }
        }.toSet()
        assertEquals(expected, report.entries.map { it.id }.toSet())
    }

    private fun summary(vararg edges: PathEdge): StatementSummary =
        StatementSummary(edges.map { it.from.base }.toSet(), edges.map(MicroEdge::of), emptyList(), emptyMap())

    private fun rule(id: String): CommonTaintConfigurationSink = object : CommonTaintConfigurationSink {
        override val id = id
        override val meta = object : CommonTaintConfigurationSinkMeta {
            override val message = id
            override val severity = CommonTaintConfigurationSinkMeta.Severity.Warning
        }
    }

    private fun source(fact: PathFact): PathEdge = PathEdge(ZERO_FACT, fact, ExclusionSet.Empty)

    /** Cached rules stay FULL. These expectations name the selected run-1 execution atom. */
    private fun grouped(f: FiniteProgramFixtures, fact: PathFact): PathFact {
        val full = (fact.mark as MarkSlot.Concrete).mark
        return fact.copy(mark = MarkSlot.Concrete(f.ap.marks.group(f.ap.marks.groupOf(full))))
    }

    private fun rules(vararg sinks: SinkRule): RuleStatement =
        RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, sinks.toList())

    private fun call(callee: MethodKey): CallPlan = CallPlan(setOf(x, y), listOf(
        CallStage.Edges(BEFORE, BOUND, BIND_IN, summary(keepEdge(x), keepEdge(y), ZERO_KEEP)),
        CallStage.Actions(BOUND, ADDED, emptyList()),
        CallStage.Callees(ADDED, RETURNED, listOf(callee)),
        CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
        CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, summary(keepEdge(x), keepEdge(y), ZERO_KEEP)),
    ), emptyList(), BEFORE, AFTER)

    /** These are primitive AP cleaners, outside the JVM's lowered field-action mapping. */
    private fun unresolved(actions: List<CleanStep> = emptyList()): CallPlan = CallPlan(setOf(x), listOf(
        CallStage.Edges(BEFORE, BOUND, BIND_IN, summary(keepEdge(x), ZERO_KEEP)),
        CallStage.Actions(BOUND, ADDED, actions),
        CallStage.Edges(ADDED, RETURNED, UNRESOLVED, summary(keepEdge(x), ZERO_KEEP)),
        CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
        CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, summary(keepEdge(x), ZERO_KEEP)),
    ), emptyList(), BEFORE, AFTER)

    private fun joined(f: FiniteProgramFixtures, config: RunConfig): RunResult<RunMethodAnalyzer> {
        val handlers = RunMethodHandlers(MethodLocalServicesFactory(::RunMethodLocalServices),
            MethodCallServicesFactory(::RunMethodCallServices))
        inputs.clear()
        val observed = RunnerHandlerFactory<RunMethodAnalyzer> { port -> handlers.create(
            object : RunnerPort<RunMethodAnalyzer> by port {
                override fun subscribe(sub: Subscription) {
                    if (config.restricted && !sub.zeroOnly) f.ops.leaves(sub.added).forEach {
                        inputs += sub.callee to Link(it, sub.linkLayer, sub.ref)
                    }
                    port.subscribe(sub)
                }
                override fun link(callee: MethodKey, ref: CallerRef, linkLayer: Layer, added: Facts) {
                    f.ops.leaves(added).forEach { inputs += callee to Link(it, linkLayer, ref) }
                    port.link(callee, ref, linkLayer, added)
                }
            }) }
        val manager = RunManager(config, f.shared, observed, quantum = 1)
        val result = manager.run(10.seconds)
        assertEquals(RunStatus.COMPLETE, result.status, f.describe())
        assertEquals(Direction.FORWARD, result.direction)
        assertEquals(config.index, result.runIndex)
        assertTrue(manager.ended)
        assertEquals(0L, manager.inFlight.pending)
        assertTrue(result.analyzers.isNotEmpty())
        for (actor in result.analyzers) {
            assertFailsWith<IllegalStateException> { actor.edges }
            assertFailsWith<IllegalStateException> { actor.initials }
        }
        return result
    }

    private fun checkTerminal(f: FiniteProgramFixtures, result: RunResult<RunMethodAnalyzer>, method: MethodKey,
                              premises: List<PremiseKey>, conclusions: List<Conclusion>): TargetSummary {
        val actor = result.analyzers.single { it.key == method }
        val row = actor.targets.single()
        var original: PremiseKey = f.ap.zero
        for (premise in premises) original = f.ap.union(original, premise)
        assertSame(original, row.premise)
        if (conclusions.any { it.demand }) assertEquals(Target.DemandTarget, row.target)
        else assertIs<Target.NormalTarget>(row.target)
        return row
    }

    @Test fun `a joined root zero group exact sink emits anonymous refinement demand`(): Unit {
        FiniteProgramFixtures().use { f ->
            val method = f.method("rootExact", listOf(listOf(1), emptyList()), 1)
            val key = method.key("root context")
            val t = MarkSlot.Concrete(f.mark("T"))
            val field = f.field("one field")
            val target = PathFact(x, listOf(field), Tail.EXACT, t)
            val forward = source(target)
            val sink = SinkRule(rule("root-exact"), 0, listOf(Pattern(target, ExclusionSet.Empty)), emptyList())
            f.entry(key, RuleStatement(summary(ZERO_KEEP, forward), StatementSummary.EMPTY, emptyList()))
            f.exit(key, 1, ExitRules(rules(sink), false, emptySet()))
            val config = f.config(L = 1, roots = listOf(key))
            val result = joined(f, config)
            assertEquals(listOf(key), result.analyzers.map { it.key })
            assertTrue(links(result.analyzers.single().key).isEmpty())
            val terminal = checkTerminal(f, result, key, listOf(f.ap.zero),
                listOf(Conclusion(grouped(f, target), ExclusionSet.Empty, true)))

            val support = historical(result, config, f)
            assertTrue(support.isSupported(key, listOf(f.ap.zero)))
            assertFalse(support.isSupported(key, listOf(f.ap.initial(sink.patterns.single()))),
                "A root's nonzero member has no root base case")
            candidateReport(config, result, f)
            assertEquals(Target.DemandTarget, terminal.target)
        }
    }

    @Test fun `a selected exact cleaner preserves the group demand despite supported zero`(): Unit {
        FiniteProgramFixtures().use { f ->
            val method = f.method("rootPartialCleaner", listOf(listOf(1), listOf(2), emptyList()), 2)
            val key = method.key()
            val t = MarkSlot.Concrete(f.mark("T"))
            val target = PathFact(x, emptyList(), Tail.ANY_TAINT, t)
            val sink = SinkRule(rule("root-demand"), 0, listOf(f.pattern(x, mark = t)), emptyList())
            f.entry(key, RuleStatement(summary(ZERO_KEEP, source(target)), StatementSummary.EMPTY, emptyList()))
            f.call(key, 1, unresolved(listOf(CleanStep.Clean(Cleaner(x, null, CleanReach.EXACT, t.mark)))))
            f.exit(key, 2, ExitRules(rules(sink), false, emptySet()))
            val config = f.config(L = 1, roots = listOf(key))
            val result = joined(f, config)
            assertTrue(links(result.analyzers.single().key).isEmpty())
            val demand = Conclusion(grouped(f, target), ExclusionSet.Empty, true)
            val terminal = checkTerminal(f, result, key, listOf(f.ap.zero), listOf(demand))
            assertTrue(result.demandLayerEdges > 0L)

            val support = historical(result, config, f)
            assertTrue(support.isSupported(key, listOf(f.ap.zero)))
            candidateReport(config, result, f)
            assertEquals(Target.DemandTarget, terminal.target,
                "Supported premises do not change a DEMAND sink edge into NORMAL")
        }
    }

    @Test fun `seeded restricted concrete inputs preserve full joint terminal support`(): Unit {
        FiniteProgramFixtures(threads = 2).use { f ->
            val main = f.method("jointCaller", listOf(listOf(1), listOf(2), emptyList()), 2)
            val target = f.method("jointCallee", listOf(listOf(1), emptyList()), 1)
            val caller = main.key("caller context")
            val callee = target.key("callee context")
            val t = MarkSlot.Concrete(f.mark("T"))
            val u = MarkSlot.Concrete(f.mark("U"))
            val px = f.pattern(x, mark = t)
            val py = f.pattern(y, mark = u)
            val sourceX = source(px.fact)
            val sourceY = source(py.fact)
            val sink = SinkRule(rule("joint-positive"), 3, listOf(px, py), emptyList())
            f.entry(caller, RuleStatement(summary(ZERO_KEEP, sourceX, sourceY), StatementSummary.EMPTY, emptyList()))
            f.call(caller, 1, call(callee))
            f.exit(callee, 1, ExitRules(rules(sink), false, emptySet()))
            val seeds = listOf(Seed.Source(caller, main.inst(0), sourceX), Seed.Source(caller, main.inst(0), sourceY))
            val config = f.config(index = 3, L = 2, roots = listOf(caller),
                demand = listOf(caller to DemandPattern(ZERO_PATTERN, ZERO_PATTERN),
                    callee to DemandPattern(ZERO_PATTERN, ZERO_PATTERN),
                    callee to DemandPattern(px, null), callee to DemandPattern(py, null)), seeds = seeds)
            assertTrue(config.seeds.allowsSource(caller, main.inst(0), sourceX))
            assertTrue(config.seeds.allowsSource(caller, main.inst(0), sourceY))
            val result = joined(f, config)
            assertEquals(setOf(caller, callee), result.analyzers.map { it.key }.toSet())
            val calleeActor = result.analyzers.single { it.key == callee }
            val ref = CallerRef(caller, f.ap.zero, Layer.NORMAL, main.inst(1), stageOrdinal = 2)
            assertEquals(setOf(Link(ZERO_PATTERN, Layer.NORMAL, ref), Link(px, Layer.NORMAL, ref),
                Link(py, Layer.NORMAL, ref)), links(calleeActor.key))
            val jx = f.ap.initial(px)
            val jy = f.ap.initial(py)
            val terminal = checkTerminal(f, result, callee, listOf(jx, jy),
                listOf(Conclusion(px.fact, px.exclusion, false), Conclusion(py.fact, py.exclusion, false)))
            val descriptor = f.shared.reportCatalog.descriptor(assertIs<Target.NormalTarget>(terminal.target).id)
            assertEquals(SinkKey(callee.method, target.inst(1), sink.rule.id), descriptor.key)

            val support = historical(result, config, f)
            assertTrue(support.isSupported(callee, listOf(jx, jy)),
                "Different caller edges at one call jointly supply every literal")
            candidateReport(config, result, f)
            assertIs<Target.NormalTarget>(terminal.target)
        }
    }

    @Test fun `normal literals arriving from different callers or different sites cannot confirm one joint sink`(): Unit {
        for (differentCallers in listOf(true, false)) FiniteProgramFixtures(threads = 3).use { f ->
            val target = f.method("splitCallee", listOf(listOf(1), emptyList()), 1)
            val callee = target.key("shared callee context")
            val t = MarkSlot.Concrete(f.mark("T"))
            val u = MarkSlot.Concrete(f.mark("U"))
            val px = f.pattern(x, mark = t)
            val py = f.pattern(y, mark = u)
            val sourceX = source(px.fact)
            val sourceY = source(py.fact)
            val sink = SinkRule(rule("joint-negative"), 0, listOf(px, py), emptyList())
            f.exit(callee, 1, ExitRules(rules(sink), false, emptySet()))
            val roots: List<MethodKey>
            val seeds: List<Seed>
            val refX: CallerRef
            val refY: CallerRef
            if (differentCallers) {
                val left = f.method("leftCaller", listOf(listOf(1), listOf(2), emptyList()), 2)
                val right = f.method("rightCaller", listOf(listOf(1), listOf(2), emptyList()), 2)
                val callerX = left.key("left context")
                val callerY = right.key("right context")
                f.entry(callerX, RuleStatement(summary(ZERO_KEEP, sourceX), StatementSummary.EMPTY, emptyList()))
                f.entry(callerY, RuleStatement(summary(ZERO_KEEP, sourceY), StatementSummary.EMPTY, emptyList()))
                f.call(callerX, 1, call(callee))
                f.call(callerY, 1, call(callee))
                roots = listOf(callerX, callerY)
                seeds = listOf(Seed.Source(callerX, left.inst(0), sourceX), Seed.Source(callerY, right.inst(0), sourceY))
                refX = CallerRef(callerX, f.ap.zero, Layer.NORMAL, left.inst(1), stageOrdinal = 2)
                refY = CallerRef(callerY, f.ap.zero, Layer.NORMAL, right.inst(1), stageOrdinal = 2)
            } else {
                val main = f.method("twoSites", listOf(listOf(1, 3), listOf(2), listOf(5),
                    listOf(4), listOf(5), emptyList()), 5)
                val caller = main.key("one caller context")
                f.statement(caller, 1, summary(ZERO_KEEP, sourceX))
                f.statement(caller, 3, summary(ZERO_KEEP, sourceY))
                f.call(caller, 2, call(callee))
                f.call(caller, 4, call(callee))
                roots = listOf(caller)
                seeds = listOf(Seed.Source(caller, main.inst(1), sourceX), Seed.Source(caller, main.inst(3), sourceY))
                refX = CallerRef(caller, f.ap.zero, Layer.NORMAL, main.inst(2), stageOrdinal = 2)
                refY = CallerRef(caller, f.ap.zero, Layer.NORMAL, main.inst(4), stageOrdinal = 2)
            }
            val config = f.config(index = 3, L = 2, roots = roots,
                demand = roots.map { it to DemandPattern(ZERO_PATTERN, ZERO_PATTERN) } + listOf(
                    callee to DemandPattern(ZERO_PATTERN, ZERO_PATTERN),
                    callee to DemandPattern(px, null), callee to DemandPattern(py, null)), seeds = seeds)
            val result = joined(f, config)
            val calleeActor = result.analyzers.single { it.key == callee }
            assertEquals(setOf(Link(ZERO_PATTERN, Layer.NORMAL, refX), Link(ZERO_PATTERN, Layer.NORMAL, refY),
                Link(px, Layer.NORMAL, refX), Link(py, Layer.NORMAL, refY)), links(calleeActor.key))
            assertNotEquals(refX, refY)
            assertEquals(differentCallers, refX.caller != refY.caller)
            assertNotEquals(refX.call, refY.call)
            val jx = f.ap.initial(px)
            val jy = f.ap.initial(py)
            val terminal = checkTerminal(f, result, callee, listOf(jx, jy),
                listOf(Conclusion(px.fact, px.exclusion, false), Conclusion(py.fact, py.exclusion, false)))
            assertTrue(result.analyzers.filter { it.key in roots }.all { actor ->
                actor.targets.none { it.premise.isZero && it.target is Target.NormalTarget }
            }, "The full joint terminal cannot combine input members from different call sites")

            val support = historical(result, config, f)
            assertTrue(support.isSupported(callee, listOf(jx)))
            assertTrue(support.isSupported(callee, listOf(jy)))
            assertFalse(support.isSupported(callee, listOf(jx, jy)),
                "The witness retains the whole premise set; singleton support at different sites is insufficient")
            candidateReport(config, result, f)
            assertIs<Target.NormalTarget>(terminal.target)
        }
    }

    @Test fun `anonymous terminal dedup retains each complete rule seed across contexts`(): Unit {
        FiniteProgramFixtures().use { f ->
            val method = f.method("contextualRoot", listOf(listOf(1), listOf(2), emptyList()), 2)
            val exactContext = method.key("normal exact context")
            val demandContext = method.key("partial must context")
            val t = MarkSlot.Concrete(f.mark("T"))
            val exact = f.pattern(x, mark = t)
            val must = exact.fact.copy(tail = Tail.ANY_TAINT)
            val primary = rule("context alternatives")
            val secondary = rule("separate vulnerability")
            val sinks = listOf(SinkRule(primary, 0, listOf(exact), emptyList()),
                SinkRule(primary, 1, listOf(exact.copy(fact = exact.fact.copy(tail = Tail.ANY))), emptyList()),
                SinkRule(secondary, 0, listOf(exact), emptyList()))
            f.entry(exactContext, RuleStatement(summary(ZERO_KEEP, source(exact.fact)), StatementSummary.EMPTY, emptyList()))
            f.entry(demandContext, RuleStatement(summary(ZERO_KEEP, source(must)), StatementSummary.EMPTY, emptyList()))
            f.call(exactContext, 1, unresolved())
            f.call(demandContext, 1, unresolved(listOf(CleanStep.Clean(Cleaner(x, null, CleanReach.EXACT, t.mark)))))
            for (key in listOf(exactContext, demandContext)) f.exit(key, 2, ExitRules(rules(*sinks.toTypedArray()), false, emptySet()))
            val config = f.config(L = 1, roots = listOf(exactContext, demandContext))
            val result = joined(f, config)
            assertEquals(setOf(exactContext, demandContext), result.analyzers.map { it.key }.toSet())
            assertTrue(result.analyzers.all { links(it.key).isEmpty() })
            for (actor in result.analyzers) {
                assertEquals(setOf(TargetSummary(f.ap.zero, Target.DemandTarget)), actor.targets)
                assertEquals(setOf(primary, secondary),
                    actor.sinkSeeds.filterIsInstance<Seed.Sink>().map { it.rule }.toSet())
                assertEquals(3, actor.sinkSeeds.size, "Distinct rule and condition seed values survive Target dedup")
            }
            candidateReport(config, result, f)

        }
    }
    @Test fun `mixed caller sink keeps its joint candidate while empty end actions create no derived source`(): Unit {
        FiniteProgramFixtures(threads = 3).use { f ->
            val left = f.method("end left", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val right = f.method("end right", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val callee = f.method("pooled end", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val t = MarkSlot.Concrete(f.mark("end T"))
            val u = MarkSlot.Concrete(f.mark("end U"))
            val v = MarkSlot.Concrete(f.mark("end V"))
            val px = f.pattern(x, mark = t)
            val py = f.pattern(y, mark = u)
            val output = f.pattern(AccessPathBase.Return, mark = v)
            val sx = source(px.fact)
            val sy = source(py.fact)
            f.entry(left, RuleStatement(summary(ZERO_KEEP, sx), StatementSummary.EMPTY, emptyList()))
            f.entry(right, RuleStatement(summary(ZERO_KEEP, sy), StatementSummary.EMPTY, emptyList()))
            f.call(left, 1, call(callee))
            f.call(right, 1, call(callee))
            val pooled = SinkRule(rule("pooled trigger"), 0, listOf(px, py), emptyList())
            val keep = summary(keepEdge(x), keepEdge(y), keepEdge(AccessPathBase.Return), ZERO_KEEP)
            f.call(callee, 1, CallPlan(setOf(x, y, AccessPathBase.Return), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, keep),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED, keep),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, keep),
            ), listOf(pooled), BEFORE, AFTER))
            val derived = SinkRule(rule("zero GEN candidate"), 0, listOf(output), emptyList())
            f.exit(callee, 2, ExitRules(rules(derived), false, emptySet()))
            val config = f.config(index = 3, L = 2, roots = listOf(left, right),
                demand = listOf(left to DemandPattern(ZERO_PATTERN, ZERO_PATTERN),
                    right to DemandPattern(ZERO_PATTERN, ZERO_PATTERN), callee to DemandPattern(ZERO_PATTERN, ZERO_PATTERN),
                    callee to DemandPattern(px, null), callee to DemandPattern(py, null)),
                seeds = listOf(Seed.Source(left, f.inst(left, 0), sx), Seed.Source(right, f.inst(right, 0), sy)))
            val result = joined(f, config)
            val calleeActor = result.analyzers.single { it.key == callee }
            val terminal = calleeActor.targets.single()
            assertSame(f.ap.union(f.ap.initial(px), f.ap.initial(py)), terminal.premise)
            val descriptor = f.shared.reportCatalog.descriptor(assertIs<Target.NormalTarget>(terminal.target).id)
            assertEquals(pooled.rule.id, descriptor.key.ruleId)
            assertFalse(historical(result, config, f).isSupported(callee, terminal.premise.members),
                "Different callers supply separate members, never the full AND at one call")
            val emitted = result.analyzers.single { it.key == callee }.summaries.all().filter { it.first.isZero }
                .flatMap { (_, facts) -> f.ops.leaves(facts) }.toSet()
            assertFalse(output in emitted, "A sink cannot manufacture an end-action source")
            assertTrue(pooled.endFacts.isEmpty())
            assertTrue(calleeActor.targets.none { row ->
                val id = (row.target as? Target.NormalTarget)?.id
                id != null && f.shared.reportCatalog.descriptor(id).key.ruleId == derived.rule.id
            }, "No downstream output terminal exists")
            candidateReport(config, result, f)
        }
    }

}
