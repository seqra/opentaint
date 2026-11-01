package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.engine.Target

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.*
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Direct Group F1 operations plus independent ordinary Full B2/F3 closure checks. */
class StaticCatalogIterationTest {
    private val returned = AccessPathBase.Return
    private val result = AccessPathBase.Argument(1)

    private data class Program(val roots: List<MethodKey>, val callee: MethodKey, val sink: SinkRule,
                               val fields: List<Int>, val marks: List<TaintMark>, val output: PathFact,
                               val sources: Set<PathEdge>)

    private fun program(f: DriverFixtures, crossed: Boolean): Program {
        val p = f.program
        p.enableGroupRuleViews()
        val roots = List(if (crossed) 2 else 1) { index ->
            p.method("catalog root $index", listOf(listOf(1), listOf(2), emptyList()), 2).key("root $index")
        }
        val callee = p.method("catalog NNF callee", listOf(listOf(1), emptyList()), 1).key("callee context")
        val cls = p.ap.accessors.index(ClassStaticAccessor("Box"))
        val sf = p.field("static f"); val sg = p.field("static g")
        val a = p.field("result a"); val b = p.field("result b")
        val t = MarkSlot.Concrete(p.mark("T")); val u = MarkSlot.Concrete(p.mark("U"))
        val v = MarkSlot.Concrete(p.mark("V")); val end = MarkSlot.Concrete(p.mark("End"))
        val first = p.pattern(STATIC, listOf(cls, sf), mark = t)
        val second = p.pattern(STATIC, listOf(cls, sg), mark = u)
        val sources = listOf(first, second).map { PathEdge(ZERO_FACT, it.fact, ExclusionSet.Empty) }
        val call = CallPlan(setOf(STATIC, returned, result), listOf(
            CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(keepEdge(STATIC), ZERO_KEEP)),
            CallStage.Actions(BOUND, ADDED, emptyList()), CallStage.Callees(ADDED, RETURNED, listOf(callee)),
            CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
            CallStage.Edges(REWRITTEN, AFTER, BIND_BACK,
                f.summary(keepEdge(STATIC), starEdge(returned, emptyList(), result, emptyList()), ZERO_KEEP)),
        ), emptyList(), BEFORE, AFTER)
        for ((index, root) in roots.withIndex()) {
            val selected = if (crossed) listOf(sources[index]) else sources
            val summary = f.summary(*(listOf(ZERO_KEEP) + selected).toTypedArray())
            val writes = selected.mapIndexed { ordinal, edge -> StaticOperation.Write(
                OperationId(FormKey(FormOwner(), root.method, root, p.inst(root, 0)), ordinal),
                Pattern(edge.to, ExclusionSet.Empty), edge) }
            p.entry(root, RuleStatement(summary.withStaticOperations(writes), StatementSummary.EMPTY, emptyList()))
            p.call(root, 1, call)
        }
        val node = p.inst(callee, 1)
        val form = FormKey(FormOwner(), callee.method, callee, node)
        val sourceId = RuleOccurrenceId(form, RuleKind.EXIT_SOURCE, 0)
        val sourceBuilder = RulePredicate.Builder(p.cancellation, p.ap.marks)
        val one = sourceBuilder.leaf(first); val two = sourceBuilder.leaf(second)
        val sourceCondition = sourceBuilder.build(sourceBuilder.and(listOf(one, sourceBuilder.or(listOf(two, two)))))
        val output = p.pattern(returned, listOf(a, b), mark = v).fact
        val source = SourceRuleOccurrence(sourceId, sourceCondition,
            listOf(SourceAction(ActionId(sourceId, ActionRole.SOURCE, 0), output)))
        val sinkBuilder = RulePredicate.Builder(p.cancellation, p.ap.marks)
        val value = sinkBuilder.leaf(Pattern(output, ExclusionSet.Empty))
        val state = sinkBuilder.leaf(second)
        val condition = sinkBuilder.build(sinkBuilder.or(listOf(value, sinkBuilder.and(listOf(value, state)))))
        val endFact = p.pattern(returned, mark = end).fact
        val endEdge = MicroEdge.of(PathEdge(ZERO_FACT, endFact, ExclusionSet.Empty))
        val sink = SinkRule(f.rule("catalog NNF sink"), 0, condition.leaves, listOf(endEdge),
            RuleOccurrenceId(form, RuleKind.EXIT_SINK, 0), condition)
        val body = StatementSummary(setOf(returned), listOf(MicroEdge.of(ZERO_KEEP)), emptyList(), emptyMap(),
            sources = listOf(source), staticOperations = listOf(
                StaticOperation.MarkInput(OperationId(form, 0), first),
                StaticOperation.MarkInput(OperationId(form, 1), second)))
        p.exit(callee, 1, ExitRules(RuleStatement(body,
            StatementSummary(emptySet(), listOf(endEdge), emptyList(), emptyMap()), listOf(sink)), true, emptySet()))
        return Program(roots, callee, sink, listOf(cls, sf, sg, a, b), listOf(t.mark, u.mark, v.mark, end.mark),
            output, sources.toSet())
    }

    private fun retained(result: RunResult<RunMethodAnalyzer>, ops: ApOps): RunObservation = RunObservation(
        rawSummaries = result.analyzers.flatMap { actor -> actor.summaries.all().flatMap { (pr, facts) ->
            observedEdges(ops, actor.key, pr, facts).asSequence()
        }.toList() }.toSet(),
        selectedDemand = result.analyzers.flatMap { actor -> actor.summaries.demandEdges(actor.mode.direction).flatMap { (pr, facts) ->
            observedEdges(ops, actor.key, pr, facts).asSequence()
        }.toList() }.toSet(),
        sourceHits = result.analyzers.flatMap { actor -> actor.sourceHits?.entries()?.map { (method, node, edge) ->
            ObservedSourceHit(method, node, edge)
        }?.toList().orEmpty() }.toSet(),
    )

    /** Additional field FLOW records can refine the root policy without changing its complete
     *  relation. Native records are compared as direction/method/kind-scoped pair unions here;
     *  full premise/literal/caller headers remain checked by the actual witnesses and closure tests. */
    private fun nativeRelations(rows: List<RawRecord>, universe: BoundedDenotation): Map<Triple<MethodKey, Direction,
        ObservationComponent>, Set<TestLocationPair>> = rows.groupBy { record ->
        Triple(record.method, record.direction, when {
            record.conclusion.fact.base == AccessPathBase.Zero -> ObservationComponent.REACH
            record.conclusion.fact.mark is MarkSlot.Star -> ObservationComponent.FLOW
            record.conclusion.fact.tail == Tail.EXACT -> ObservationComponent.NORMAL_EXACT
            else -> ObservationComponent.NORMAL_MUST
        })
    }.mapValues { (_, records) -> records.flatMap { universe.pairs(it.premise, it.conclusion) }.toSet() }

    /** Plain copies of phase inputs, without a production driver, demand index or record selector in the oracle. */
    private fun phaseInputs(f: DriverFixtures, p: Program, config: RunConfig,
                            universe: BoundedDenotation): ProgramRunInputs {
        val owners = p.roots + p.callee
        val demands = owners.flatMap { owner -> universe.positions.flatMap { position ->
            // Query-specific static guidance is observed through the known FULL test universe.
            val marks: List<MarkSlot> = if (position.base == STATIC) listOf(MarkSlot.STAR) +
                universe.marks.filter { f.manager.marks.fullId(it) != null }.map { MarkSlot.Concrete(it) }
                else listOf(MarkSlot.STAR)
            marks.flatMap { mark ->
                val initial = if (position.base == AccessPathBase.Zero) f.manager.zero
                            else f.manager.initial(demandProbe(position.base, position.path, mark))
                val probe = initial.toPattern()
                // This is a family at the actual position, not a stored universal row.
                val carry = if (config.demand?.hasSharedStaticCarry == true && probe.fact.base == STATIC)
                    DemandPattern(probe, probe) else null
                config.demand?.covering(owner, initial).orEmpty().filter { it != carry }.map { owner to it }
            }
        } }.distinct()
        val records = owners.flatMap { owner -> universe.positions.flatMap { position ->
            config.records.byEntry(owner, f.program.pattern(position.base, position.path, Tail.STAR, MarkSlot.STAR)).toList()
        } }.distinct().flatMap { record -> f.ops.leaves(record.conclusion).map {
            RawRecord(record.method, record.direction, record.premise.toPattern(), Conclusion(it.fact, it.exclusion, false))
        }.toList() }
        val seeds = owners.flatMap { owner -> f.program.programMethod(owner).successors.indices.flatMap { index ->
            config.seeds.at(owner, f.program.inst(owner, index))
        } }
        return ProgramRunInputs(p.roots, demands, records, seeds,
            hasSharedStaticCarry = config.demand?.hasSharedStaticCarry == true)
    }

    @Test
    fun `direct static NNF candidates retain full refinement source seeds records and complete guard bindings`(): Unit {
        for (crossed in listOf(false, true)) for (sameUnit in listOf(false, true)) DriverFixtures().use { f ->
            val p = program(f, crossed)
            val limits = listOf(1, 1, 2)
            val forward = f.program.config(roots = p.roots)
            var first: RunObservation? = null
            for (policy in listOf(SchedulePolicy.REPLAY_FIRST, SchedulePolicy.NOTIFY_FIRST)) {
                val actual = ProductionSchedule(f.program, forward, sameUnit, policy, quantum = 1,
                    duplicateDeliveries = true).run()
                assertDirectStaticProtocol(actual, f.program)
                assertTrue(actual.targets.any { !it.normal && it.method == p.callee })
                assertTrue(actual.targets.all { it.premise.size == 1 }, "Run-1 emits each atomic origin")
                assertTrue(actual.rawSummaries.none { it.conclusion.fact.mark == MarkSlot.Concrete(p.marks.last()) ||
                    it.conclusion.fact.mark == GroupedScalarMarks(f.manager.marks).slot(MarkSlot.Concrete(p.marks.last())) },
                    "Ignored END actions never create either Group or Full data")
                val out = GroupedScalarMarks(f.manager.marks).conclusion(Conclusion(p.output, ExclusionSet.Empty, true))
                val firstStatic = GroupedScalarMarks(f.manager.marks).pattern(f.program.pattern(STATIC,
                    listOf(p.fields[0], p.fields[1]), Tail.STAR, mark = MarkSlot.Concrete(p.marks[0])))
                assertTrue(actual.rawSummaries.any { it.method == p.callee && it.premise == setOf(firstStatic) &&
                    it.conclusion == limit(out, 1) }, "A complete static guard keeps its preferred original field")
                assertTrue(actual.rawSummaries.all { it.premise.size == 1 })
                first = first ?: actual
            }
            val fresh = f.program.mark("fresh")
            val universe = BoundedDenotation(listOf(AccessPathBase.Zero, STATIC, returned, result, AccessPathBase.Argument(17)),
                p.fields + f.program.field("fresh"), (p.marks + fresh + (p.marks + fresh).map { f.manager.marks.group(f.manager.marks.groupOf(it)) } + TaintMark.ZERO).distinct(), 3)
            f.program.freshShared(sameUnit).use { owner ->
                val configs = ArrayList<RunConfig>()
                val replayInputs = LinkedHashMap<Int, ProgramRunInputs>()
                val report = IterationDriver(FixedLimits(limits), owner, 20.seconds,
                    invokeRun = { config, shared, timeout ->
                        configs += config
                        // Read views share the persistent owner. Freeze before this run's barrier
                        // can add its own records; an after-analysis replay would see future records.
                        if (!config.run1) replayInputs[config.index] = phaseInputs(f, p, config, universe)
                        f.run(config, shared, timeout)
                    },
                    guardBarrier = { _, body -> body() }).analyze(p.roots)
                assertEquals(RunStatus.COMPLETE, report.end.status)
                assertEquals(listOf(1, 2, 3), f.results.map { it.runIndex })
                val expectedReports = if (crossed) emptySet() else setOf(p.sink.rule)
                assertEquals(expectedReports, report.entries.map { it.descriptor.rule }.toSet(),
                    buildString {
                        appendLine("crossed=$crossed sameUnit=$sameUnit end=${report.end}")
                        for (config in configs) {
                            appendLine("run-${config.index} ${config.direction} mode=${config.mode.markMode}")
                            for (owner in p.roots + p.callee) {
                                appendLine("demand ${owner.method.name}: ${config.demand?.explicitRows(owner)}")
                                appendLine("ZERO ${owner.method.name}: ${config.demand?.initials(owner, Reach.NORMAL, config.admissionPolicy)}")
                            }
                            for (actor in f.results.single { it.runIndex == config.index }.analyzers) {
                                appendLine("actor ${actor.key}: targets=${actor.targets} selected=${actor.outgoingTargets}")
                                appendLine("hits=${actor.sourceHits?.occurrences()?.toList()}")
                                appendLine("summaries=${actor.summaries.all().map { (origin, facts) -> origin to f.ops.leaves(facts).toList() }.toList()}")
                            }
                        }
                    })
                if (crossed) {
                    // Run-1 may combine the global static supplies. A later NORMAL
                    // terminal keeps both origins and needs one complete caller binding.
                    val last = f.results.single { it.runIndex == 3 }
                    val callee = last.analyzers.single { it.key == p.callee }
                    val expectedOrigins = setOf(
                        f.program.pattern(STATIC, listOf(p.fields[0], p.fields[1]),
                            mark = MarkSlot.Concrete(p.marks[0])),
                        f.program.pattern(STATIC, listOf(p.fields[0], p.fields[2]),
                            mark = MarkSlot.Concrete(p.marks[1])),
                    )
                    assertTrue(callee.targets.any { row -> row.target is Target.NormalTarget &&
                        row.premise.members.map { it.toPattern() }.toSet() == expectedOrigins },
                        "The local NORMAL sink must retain both exact static requirements")
                    assertTrue(last.analyzers.filter { it.key in p.roots }.none { actor ->
                        actor.targets.any { it.premise.isZero && it.target is Target.NormalTarget }
                    }, "Separate roots cannot complete the two-premise NORMAL terminal")
                }
                assertEquals(1, configs[1].seeds.size)
                val physical = assertIs<Seed.PredicateSink>(configs[1].seeds.at(p.callee, f.program.inst(p.callee, 1)).single())
                assertEquals(p.sink.occurrenceId, physical.occurrence)
                // The historical scalar closure has unconditional ZERO. It is not
                // an oracle for the selected Target-gated admission/report lanes.
                for (run in f.results) for (actor in run.analyzers) {
                    assertTrue(actor.targets.all { row -> row.premise.members.none { it.isFlow } })
                    if (run.direction == Direction.BACKWARD)
                        assertTrue(actor.targets.none { it.target is org.opentaint.dataflow.bidi.engine.Target.NormalTarget })
                }
                val backward = f.results[1].analyzers.flatMap { it.sourceHits!!.occurrences().toList() }
                for (source in p.sources) assertTrue(backward.any { it.forward == source && it.method in p.roots })
                val occurrence = f.program.forms(p.callee).exitRules(Direction.FORWARD, f.program.inst(p.callee, 1))
                    .rules.summary.sources.single()
                assertTrue(backward.filter { it.method == p.callee }.all { hit ->
                    hit.action == occurrence.actions.single().id && hit.forward.to == p.output
                }, "The later source seeds retain the full action and occurrence identity")
                val forwarded = (p.roots + p.callee).flatMap { key -> f.program.programMethod(key).successors.indices.flatMap { node ->
                    configs[2].seeds.at(key, f.program.inst(key, node)).filterIsInstance<Seed.Source>()
                } }
                assertEquals(backward.map { Seed.Source(it.method, it.statement, it.forward, it.action) }.toSet(), forwarded.toSet())

            }
        }
    }
}
