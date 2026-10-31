package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.*
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import kotlin.test.*

/** Current F77 sequences. All field transfers below use one field per statement. */
class CurrentSequenceTest {
    private val argument = AccessPathBase.Argument(0)
    private val returned = AccessPathBase.Return
    private val x = AccessPathBase.LocalVar(0)
    private val r = AccessPathBase.LocalVar(1)

    private fun straight(size: Int): List<List<Int>> = List(size) { if (it + 1 < size) listOf(it + 1) else emptyList() }
    private fun sources(f: DriverFixtures, key: MethodKey, vararg edges: PathEdge) {
        f.program.entry(key, RuleStatement(f.summary(ZERO_KEEP, *edges), StatementSummary.EMPTY, emptyList()))
    }
    private fun sink(f: DriverFixtures, id: String, p: Pattern, ends: List<MicroEdge> = emptyList()): SinkRule =
        SinkRule(f.rule(id), 0, listOf(p), ends)
    private fun exit(f: DriverFixtures, key: MethodKey, index: Int, vararg sinks: SinkRule) {
        f.program.exit(key, index, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
            sinks.toList()), false, emptySet()))
    }
    private fun resolved(f: DriverFixtures, callee: MethodKey, bindings: List<Pair<AccessPathBase, AccessPathBase>>,
                         target: AccessPathBase): CallPlan = CallPlan(bindings.map { it.first }.toSet() + target, listOf(
        CallStage.Edges(BEFORE, AFTER, PASS_OVER,
            f.summary(*bindings.map { keepEdge(it.first) }.toTypedArray())),
        CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP,
            *bindings.map { starEdge(it.first, emptyList(), it.second, emptyList()) }.toTypedArray())),
        CallStage.Actions(BOUND, ADDED, emptyList()),
        CallStage.Callees(ADDED, RETURNED, listOf(callee)),
        CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
        CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP,
            starEdge(returned, emptyList(), target, emptyList()))),
    ), emptyList(), BEFORE, AFTER)
    private fun raw(f: DriverFixtures, result: RunResult<RunMethodAnalyzer>, key: MethodKey): Set<Pair<Set<Pattern>, Conclusion>> =
        result.analyzers.single { it.key == key }.summaries.all().flatMap { (premise, facts) ->
            f.ops.leaves(facts).map { premise.members.map { it.toPattern() }.toSet() to
                Conclusion(it.fact, it.exclusion, facts.layer == Layer.DEMAND) }
        }.toSet()
    private fun selected(f: DriverFixtures, result: RunResult<RunMethodAnalyzer>, key: MethodKey): Set<Pair<Set<Pattern>, Conclusion>> =
        result.analyzers.single { it.key == key }.summaries.demandEdges().flatMap { (premise, facts) ->
            f.ops.leaves(facts).map { premise.members.map { it.toPattern() }.toSet() to
                Conclusion(it.fact, it.exclusion, facts.layer == Layer.DEMAND) }
        }.toSet()

    private fun terminalRules(f: DriverFixtures, result: RunResult<RunMethodAnalyzer>,
                              catalog: ReportCatalog = f.shared.reportCatalog): Set<String> =
        result.analyzers.flatMap { actor ->
            actor.targets.mapNotNull { row -> (row.target as? Target.NormalTarget)?.let {
                catalog.descriptor(it.id).key.ruleId
            } } + actor.sinkSeeds.mapNotNull { (it as? Seed.Sink)?.rule?.id }
        }.toSet()

    /** Negative control: remove only the backward conjunction demotion from the cached form. */
    private fun normalConjunctionReversal(f: DriverFixtures, method: MethodKey): SharedObjects {
        val original = f.shared
        val contextSource = object : MethodContextSource {
            private val changed = object : MethodForms by f.program.forms(method) {
                private var cached: CallPlan? = null
                override fun <R> withCall(direction: Direction, s: CommonInst, call: CommonCallExpr,
                                          use: (CallPlan) -> R): R = use(call(direction, s, call))
                override fun call(direction: Direction, s: CommonInst, call: CommonCallExpr): CallPlan {
                    val actual = f.program.forms(method).call(direction, s, call)
                    if (direction != Direction.BACKWARD) return actual
                    return cached ?: CallPlan(actual.touched, actual.stages.map { stage ->
                        if (stage !is CallStage.Edges) stage else stage.copy(summary = StatementSummary(
                            stage.summary.touched, stage.summary.edges.map { edge ->
                                if (!edge.conjunctive) edge else MicroEdge(edge.edge, edge.forward, conjunctive = false)
                            }, stage.summary.conjunctions, stage.summary.typeFilters, stage.summary.resultFilters))
                    }, actual.sinks, actual.entry, actual.exit, actual.passReads).also { cached = it }
                }
            }
            override fun forms(key: MethodKey): MethodForms = if (key == method) changed else f.program.forms(key)
            override fun graph(key: MethodKey, direction: Direction) = f.program.graph(key, direction)
        }
        return SharedObjects(original.ap, original.ops, original.interpreter, original.language,
            MethodContextCache(original.interpreter, contextSource), original.records,
            original.unitResolver, original.refManager, original.cancellation, threads = 1)
    }

    @Test
    fun `WRAP reuses normal FLOW records while Target demand guides the remaining refinements`(): Unit {
        DriverFixtures().use { f ->
            val p = f.program
            val root = p.method("WRAP root", straight(3), 2).key()
            val wrap = p.method("WRAP callee", straight(4), 3).key()
            val a = p.field("a"); val b = p.field("b"); val c = p.field("c"); val field = p.field("f")
            val mark = MarkSlot.Concrete(p.mark("WRAP T"))
            val source = PathEdge(ZERO_FACT, PathFact(x, listOf(a, b, c), Tail.EXACT, mark), ExclusionSet.Empty)
            sources(f, root, source)
            val z = AccessPathBase.LocalVar(2)
            p.statement(wrap, 1, MicroEdgeBuilder().apply { write(z, listOf(field), false, listOf(argument), emptyList()) }.build())
            p.statement(wrap, 2, MicroEdgeBuilder().apply { move(returned, z) }.build())
            p.call(root, 1, resolved(f, wrap, listOf(x to argument), r))
            val finding = sink(f, "WRAP sink", p.pattern(r, listOf(field, a, b, c), mark = mark))
            exit(f, root, 2, finding)
            val driver = f.driver(FixedLimits(listOf(1, 1, 2, 3, 4)))
            val report = driver.analyze(listOf(root))
            assertEquals(listOf(1, 2, 3, 4, 5), f.configs.map { it.index })
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 5, Direction.FORWARD, EndReason.NO_DEMAND_EDGE), report.end)
            assertEquals(finding.rule.id, report.entries.single().descriptor.key.ruleId)
            val from = p.pattern(argument, tail = Tail.STAR, mark = MarkSlot.STAR)
            val to = Conclusion(PathFact(returned, listOf(field), Tail.STAR, MarkSlot.STAR), ExclusionSet.Empty, false)
            assertContains(raw(f, f.results[0], wrap), setOf(from) to to)
            assertTrue(selected(f, f.results[0], wrap).isEmpty(),
                "Normal singleton FLOW summaries persist as records and are not selected demand")
            val scalar = DirectCurrentIteration(p, listOf(root), listOf(1, 1, 2, 3, 4)).run()
            assertEquals(listOf(1, 2, 3), scalar.runs.map { it.index },
                "The explicit old-reference control stops when AP guidance is empty")
            val bases = listOf(AccessPathBase.Zero, STATIC, argument, returned, x, r, z)
            val universe = BoundedDenotation(bases, listOf(a, b, c, field, p.field("fresh")),
                listOf(mark.mark, p.mark("fresh"), TaintMark.ZERO), 4)
            for ((actual, expected) in f.results.take(1).zip(scalar.runs.take(1))) {
                val actualRows = actual.analyzers.flatMap { actor -> raw(f, actual, actor.key).map { (premise, value) ->
                    ObservedEdge(actor.key, premise, value)
                } }.toSet()
                val actualGuides = actual.analyzers.flatMap { actor -> selected(f, actual, actor.key).map { (premise, value) ->
                    ObservedEdge(actor.key, premise, value)
                } }.toSet()
                RunObservation(rawSummaries = expected.observation.rawSummaries,
                    selectedDemand = expected.observation.selectedDemand).assertEquivalent(
                    RunObservation(rawSummaries = actualRows, selectedDemand = actualGuides), universe)
                if (actual.runIndex > 1) {
                    val inputs = f.processed.filter { it.run == actual.runIndex && it.method == wrap }
                    assertTrue(inputs.isNotEmpty())
                    assertTrue(inputs.all { it.delta.premise.members.all { member -> member.isZero } },
                        "Only ZERO discovery enters the wrapper; records apply its completed FLOW relation")
                    assertTrue(wrap !in driver.frontiers[actual.runIndex - 1].analysed)
                }
            }
            assertTrue(f.configs[2].seeds.allowsSource(root, root.statement, source))
            assertTrue(driver.frontiers.first().targetDemand > 0)
            assertEquals(0, driver.frontiers.last().targetDemand)
            assertTrue(driver.frontiers.last().demandEdges.isEmpty())
            assertTrue(f.results[0].analyzers.any { it.outgoingTargets.isNotEmpty() })
            assertTrue(f.records.byEntry(wrap, from).any { record ->
                record.direction == Direction.FORWARD && record.premise.toPattern() == from &&
                    record.conclusion.layer == Layer.NORMAL && f.ops.leaves(record.conclusion).any {
                        it.fact == to.fact && it.exclusion == to.exclusion
                    }
            }, "The eligible F1 NORMAL FLOW row is retained by the ordinary writer")
            assertTrue(f.results.drop(1).all { result -> result.analyzers.none { it.key == wrap && it.nonZeroInitial } })
            assertTrue(f.results.filter { it.direction == Direction.BACKWARD }.all { run ->
                run.analyzers.flatMap { it.targets }.none { it.target is Target.NormalTarget }
            })
        }
    }

    @Test
    fun `a nonreturning worker loop reports its sink without waiting for a normal summary`(): Unit {
        DriverFixtures().use { f ->
            val p = f.program
            val root = p.method("worker caller", straight(3), 2).key()
            val worker = p.method("nonreturning worker",
                listOf(listOf(1), listOf(2), listOf(1), emptyList(), emptyList()),
                normalExit = 3, exceptionalExit = 4, backwardExitDiscovery = true).key()
            val t = MarkSlot.Concrete(p.mark("worker T"))
            val source = PathEdge(ZERO_FACT, PathFact(x, emptyList(), Tail.EXACT, t), ExclusionSet.Empty)
            sources(f, root, source)
            p.call(root, 1, resolved(f, worker, listOf(x to argument), r))
            val finding = sink(f, "nonreturning worker sink", p.pattern(argument, mark = t))
            val keep = f.summary(keepEdge(argument), ZERO_KEEP)
            p.call(worker, 1, CallPlan(setOf(argument), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, keep),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED, keep),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, keep),
            ), listOf(finding), BEFORE, AFTER))
            val driver = f.driver(FixedLimits(listOf(1, 1, 2)), run1MarkMode = MarkMode.GROUP)
            val report = driver.analyze(listOf(root))
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 3, Direction.FORWARD, EndReason.NO_DEMAND_EDGE,
                run1MarkMode = MarkMode.GROUP), report.end)
            val sinkSeeds = f.configs[1].seeds.at(worker, p.inst(worker, 1))
            assertTrue(sinkSeeds.any { it is Seed.Sink && it.rule === finding.rule &&
                it.requirement == p.pattern(argument, mark = t) }, "F1 prepares the exact nonreturning-worker sink seed")
            assertTrue(f.results[0].analyzers.single { it.key == worker }.targets.any { it.target == Target.DemandTarget },
                "The group-valued source reaches the local sink")
            assertTrue(f.processed.any { it.run == 2 && it.method == worker && it.delta.node == p.inst(worker, 1) },
                "Backward ZERO discovers the sink through exceptional-only S11 wiring; " +
                    "B2workerNodes=${f.processed.filter { it.run == 2 && it.method == worker }.map { it.delta.node.location.index }} " +
                    "seeds=$sinkSeeds")
            assertContains(f.results[1].analyzers.flatMap { it.sourceHits!!.entries().toList() },
                Triple(root, root.statement, source))
            assertTrue(f.configs[2].seeds.allowsSource(root, root.statement, source))
            assertEquals(listOf(finding.rule.id), report.entries.map { it.descriptor.key.ruleId })
            val actor = f.results.first().analyzers.single { it.key == worker }
            assertTrue(actor.summaries.all().none(), "A nonreturning method has no fabricated normal-return summary")
            assertTrue(f.results.last().analyzers.single { it.key == worker }.summaries.all().none())
            assertTrue(f.links(1, actor.key).asSequence().any { it.caller.caller == root && it.linkLayer == Layer.NORMAL })
            assertTrue(f.processed.any { it.method == worker && it.delta.node == p.inst(worker, 2) })
            assertTrue(f.processed.none { it.run % 2 == 1 && it.method == worker &&
                it.delta.node in listOf(p.inst(worker, 3), p.inst(worker, 4)) },
                "Discovery wiring never adds a forward normal or exceptional return")
            assertContains(driver.frontiers.first().analysed, worker)
        }
    }

    @Test
    fun `an incomplete third run preserves a settled normal sink and does not commit demand candidates`(): Unit {
        for (status in listOf(RunStatus.TIMEOUT, RunStatus.OOM, RunStatus.FAILED)) DriverFixtures().use { f ->
            val confirmed = f.confirmed()
            val demand = f.persistentDemand()
            val unconditional = SinkRule(confirmed.rule, 0, listOf(ZERO_PATTERN), emptyList())
            f.program.exit(confirmed.root, 1, ExitRules(RuleStatement(StatementSummary.EMPTY,
                StatementSummary.EMPTY, listOf(unconditional)), false, emptySet()))
            val visited = ArrayList<Int>()
            var retainedBeforeFailure: NormalTargetView = NormalTargetView.EMPTY
            val driver = f.driver(FixedLimits(listOf(1, 1, 2)), invokeRun = { config, owner, timeout ->
                visited += config.index
                if (config.index < 3) f.run(config, owner, timeout)
                else f.manager(config, owner).let { manager ->
                    retainedBeforeFailure = config.normalTargets
                    manager.fail(status)
                    manager.run(timeout)
                }
            })
            val report = driver.analyze(listOf(confirmed.root, demand.root))
            assertEquals(listOf(1, 2, 3), visited)
            assertEquals(AnalysisEnd(status, 3, Direction.FORWARD, EndReason.ABNORMAL), report.end)
            assertEquals(listOf(confirmed.rule.id), report.entries.map { it.descriptor.key.ruleId })
            assertTrue(retainedBeforeFailure.rows().any { it.id == report.entries.single().id })
            assertEquals(listOf(1, 2), driver.frontiers.map { it.run })
            assertFalse(f.cancellation.isActive())
        }
    }

    @Test
    fun `empty end actions keep the original sink and settle its normal source in run1`(): Unit {
        DriverFixtures().use { f ->
            val p = f.program
            val root = p.method("END root", straight(3), 2).key()
            val m = p.method("END M", straight(5), 4).key()
            val t = MarkSlot.Concrete(p.mark("END T")); val u = MarkSlot.Concrete(p.mark("END U"))
            val source = PathEdge(ZERO_FACT, PathFact(x, emptyList(), Tail.EXACT, t), ExclusionSet.Empty)
            sources(f, root, source)
            p.call(root, 1, resolved(f, m, listOf(x to argument), r))
            val y = AccessPathBase.LocalVar(2); val w = AccessPathBase.LocalVar(3)
            // The finite engine receives effective forms, after the provider clears end actions.
            val early = sink(f, "END original sink", p.pattern(argument, mark = t))
            p.call(m, 1, CallPlan(setOf(argument, y), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(keepEdge(argument), ZERO_KEEP)),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED, f.summary(keepEdge(argument), ZERO_KEEP)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(starEdge(returned, emptyList(), y, emptyList()), ZERO_KEEP)),
            ), listOf(early), BEFORE, AFTER))
            val may = PathEdge(PathFact(argument, emptyList(), Tail.STAR, MarkSlot.STAR),
                PathFact(returned, emptyList(), Tail.ANY, MarkSlot.STAR), ExclusionSet.Empty)
            p.call(m, 2, CallPlan(setOf(y, w), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(starEdge(y, emptyList(), argument, emptyList()), ZERO_KEEP)),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED, f.summary(may, ZERO_KEEP)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(starEdge(returned, emptyList(), w, emptyList()), ZERO_KEEP)),
            ), emptyList(), BEFORE, AFTER))
            p.statement(m, 3, MicroEdgeBuilder().apply { move(returned, w) }.build())
            val later = sink(f, "END later demand", p.pattern(r, tail = Tail.ANY, mark = u))
            exit(f, root, 2, later)
            val driver = f.driver(FixedLimits(listOf(1, 1, 2)))
            val report = driver.analyze(listOf(root))
            assertEquals(listOf(1), f.configs.map { it.index },
                "The exact FULL source and unary sink path settle normally in run-1")
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 1, Direction.FORWARD, EndReason.NO_DEMAND_EDGE), report.end)
            assertEquals(listOf(early.rule.id), report.entries.map { it.descriptor.key.ruleId })
            val forward = f.results.single()
            assertContains(terminalRules(f, forward), early.rule.id)
            assertFalse(later.rule.id in terminalRules(f, forward), "Ignored END output must not reach the later sink")
            assertTrue(f.processed.all { row -> f.ops.leaves(row.delta.facts).none { it.fact.mark == u } },
                "No END action may produce U at any processed instruction")
            assertTrue(forward.analyzers.all { actor -> actor.triggerSeeds == 0L && actor.sinkSeeds.isEmpty() })
            assertTrue(forward.analyzers.flatMap { it.targets }.all { it.target is Target.NormalTarget })
            assertEquals(listOf(0), driver.frontiers.map { it.seeds })
            assertEquals(1, driver.frontiers.single().reportedSinks)
        }
    }

    @Test
    fun `CONJ run1 weakens caller bindings while FULL backward branches retain both requirements`(): Unit {
        for (normalReversal in listOf(false, true)) DriverFixtures().use { f ->
            val p = f.program
            p.enableGroupRuleViews()
            val root = p.method("CONJ root", straight(7), 6).key()
            val m = p.method("CONJ M", straight(2), 1).key()
            val a = x; val b = AccessPathBase.LocalVar(2); val clean = AccessPathBase.LocalVar(3)
            val z = AccessPathBase.LocalVar(4); val y = AccessPathBase.LocalVar(5); val bad = AccessPathBase.LocalVar(6)
            val arg1 = AccessPathBase.Argument(1)
            val t1 = MarkSlot.Concrete(p.mark("CONJ T1")); val t2 = MarkSlot.Concrete(p.mark("CONJ T2"))
            val t = MarkSlot.Concrete(p.mark("CONJ T"))
            val field = p.field("f"); val g = p.field("g")
            val sa = PathEdge(ZERO_FACT, PathFact(a, emptyList(), Tail.EXACT, t1), ExclusionSet.Empty)
            val sb = PathEdge(ZERO_FACT, PathFact(b, emptyList(), Tail.EXACT, t2), ExclusionSet.Empty)
            sources(f, root, sa, sb)
            val nd = ConjunctiveEdge(listOf(p.pattern(argument, mark = t1), p.pattern(arg1, mark = t2)),
                PathFact(returned, emptyList(), Tail.EXACT, t))
            // The unresolved lib call is the one statement of M.
            p.call(m, 0, CallPlan(setOf(argument, arg1, returned), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(keepEdge(argument), keepEdge(arg1), ZERO_KEEP)),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED,
                    StatementSummary(setOf(argument, arg1, returned), listOf(MicroEdge.of(ZERO_KEEP)), listOf(nd), emptyMap())),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(keepEdge(returned), ZERO_KEEP)),
            ), emptyList(), BEFORE, AFTER))
            p.call(root, 1, resolved(f, m, listOf(a to argument, b to arg1), r))
            // Build y.f.g with two one-field writes on fresh objects.
            p.statement(root, 2, MicroEdgeBuilder().apply { write(z, listOf(g), false, listOf(r), emptyList()) }.build())
            p.statement(root, 3, MicroEdgeBuilder().apply { write(y, listOf(field), false, listOf(z), emptyList()) }.build())
            p.call(root, 5, resolved(f, m, listOf(a to argument, clean to arg1), bad))
            val goodSink = sink(f, "CONJ both inputs", p.pattern(y, listOf(field, g), mark = t))
            val badSink = sink(f, "CONJ missing second input", p.pattern(bad, mark = t))
            exit(f, root, 6, goodSink, badSink)
            val control = if (normalReversal) normalConjunctionReversal(f, m) else null
            val driver = if (control == null) f.driver(FixedLimits(listOf(1, 1, 2)), run1MarkMode = MarkMode.GROUP)
                else withRun1MarkMode(MarkMode.GROUP) {
                    IterationDriver(FixedLimits(listOf(1, 1, 2)), control,
                        kotlin.time.Duration.parse("5s"), f::run, { _, body -> body() })
                }
            val report = try { driver.analyze(listOf(root)) } finally { control?.close() }
            assertEquals(listOf(1, 2, 3), f.configs.map { it.index })
            assertEquals(setOf(goodSink.patterns.single(), badSink.patterns.single()),
                f.configs[1].seeds.at(root, p.inst(root, 6)).filterIsInstance<Seed.Sink>()
                    .map { it.requirement }.toSet(),
                "GROUP run-1 retains full-mark sink seeds for the FULL backward run")
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 3, Direction.FORWARD,
                if (driver.frontiers.last().demandEdges.isEmpty()) EndReason.NO_DEMAND_EDGE else EndReason.POLICY,
                run1MarkMode = MarkMode.GROUP), report.end)
            // Exact DEMAND admissions can retain guidance after the finding is proved.
            // This bounded positive/negative control does not claim a global stop at run-3.
            assertEquals(if (normalReversal) setOf(goodSink.rule, badSink.rule) else setOf(goodSink.rule),
                report.entries.map { it.descriptor.rule }.toSet(),
                "normalReversal=$normalReversal " + f.results.joinToString("\n") { run ->
                    "run-${run.runIndex}: " + run.analyzers.joinToString { actor ->
                        "${actor.key.method.name}: targets=" + actor.targets.map { it.premise.members.map { m -> m.toPattern() } to it.target } +
                            "; AP=" + raw(f, run, actor.key) +
                            "; processed=" + f.processed.filter { it.run == run.runIndex && it.method == actor.key }
                                .map { it.delta.node.location.index to (it.delta.premise.members.map { m -> m.toPattern() } to f.ops.leaves(it.delta.facts).toList()) } +
                            "; sourceHits=" + actor.sourceHits?.occurrences()?.toList()
                    }
                })
            assertTrue(report.entries.all { it.descriptor.key.statement == p.inst(root, 6) })
            assertEquals(setOf(goodSink.rule.id, badSink.rule.id), terminalRules(f, f.results[0], control?.reportCatalog ?: f.shared.reportCatalog),
                "The run-1 singleton summary also permits the caller with only the selected input")
            assertEquals(if (normalReversal) setOf(goodSink.rule.id, badSink.rule.id) else setOf(goodSink.rule.id),
                terminalRules(f, f.results[2], control?.reportCatalog ?: f.shared.reportCatalog),
                "FULL forward analysis keeps the original complete condition")
            val required = setOf(p.pattern(argument, mark = t1), p.pattern(arg1, mark = t2))
            fun grouped(pattern: Pattern): Pattern = pattern.copy(fact = pattern.fact.copy(mark =
                MarkSlot.Concrete(p.manager.marks.group(p.manager.marks.groupOf((pattern.fact.mark as MarkSlot.Concrete).mark)))))
            val groupedTarget = grouped(Pattern(nd.target, ExclusionSet.Empty)).fact
            assertContains(raw(f, f.results[0], m), setOf(grouped(required.first())) to
                Conclusion(groupedTarget, ExclusionSet.Empty, true))
            val backward = selected(f, f.results[1], m)
            val literalRows = if (normalReversal) raw(f, f.results[1], m) else backward
            assertTrue(literalRows.any { it.second.fact == required.first().fact && it.second.demand == !normalReversal })
            assertTrue(literalRows.any { it.second.fact == required.last().fact && it.second.demand == !normalReversal })
            assertTrue(backward.filter { it.second.fact.base != AccessPathBase.Zero }.all { it.second.demand })
            if (f.configs[1].demand!!.initials(m, Reach.NORMAL, f.configs[1].admissionPolicy).isEmpty())
                assertTrue(backward.none { it.first == setOf(ZERO_PATTERN) },
                    "Admitting a concrete exact requirement cannot invent ZERO permission")
            val concreteReturn = p.pattern(returned, mark = t)
            assertEquals(normalReversal, f.records.byEntry(m, concreteReturn).any { it.direction == Direction.BACKWARD },
                "Split literal branches cannot become independent normal records")
            assertTrue(f.configs[2].demand!!.near(m, demandProbe(argument)).any { it.entry == required.first() },
                "The independent DEMAND admission retains guidance even when another lane produces native records")
            assertTrue(f.configs[2].demand!!.near(m, demandProbe(arg1)).any { it.entry == required.last() })
            assertTrue(f.configs[2].seeds.allowsSource(root, root.statement, sa))
            assertTrue(f.configs[2].seeds.allowsSource(root, root.statement, sb))
            assertTrue(f.results[2].analyzers.flatMap { it.targets }.filter { it.target is Target.NormalTarget }.isNotEmpty())
            assertTrue(f.links(3, m).asSequence().any { link ->
                link.caller.call == p.inst(root, 5) && link.addedFact == required.first() && link.linkLayer == Layer.NORMAL
            }, "Persisted replay does not suppress the live route when the current demand is also present")
            assertTrue(driver.frontiers.first().targetDemand > 0)
            assertEquals(if (normalReversal) 2 else 1, driver.frontiers.last().reportedSinks)
        }
    }
}
