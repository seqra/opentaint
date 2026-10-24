package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.CallerRef
import kotlin.test.*

/** Use the actual actor, original rule services, method stores and publication handoff. */
class FlowBackedEngineTest {
    private val x = AccessPathBase.Argument(0)
    private val z = AccessPathBase.Argument(1)
    private val ret = AccessPathBase.Return
    private fun fullCore(f: MethodAnalysisFixtures, calls: Boolean = false): RunMethodAnalyzer = f.core(
        RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL),
        localFactory = MethodLocalServicesFactory(::RunMethodLocalServices),
        callFactory = if (calls) MethodCallServicesFactory(::RunMethodCallServices) else null)
    private fun initial(f: MethodAnalysisFixtures, mark: MarkSlot) =
        f.manager.initial(f.pattern(x, tail = Tail.STAR, mark = mark))
    private fun source(f: MethodAnalysisFixtures, node: Int, ordinal: Int, from: Pattern, to: PathFact): SourceRuleOccurrence {
        val builder = RulePredicate.Builder(f.cancellation)
        val predicate = builder.build(builder.leaf(from))
        val id = RuleOccurrenceId(FormKey(FormOwner(), f.key.method, f.key, f.inst(node)), RuleKind.CALL_SOURCE, ordinal)
        return SourceRuleOccurrence(id, predicate, listOf(SourceAction(ActionId(id, ActionRole.SOURCE, 0), to)))
    }
    private fun read(f: MethodAnalysisFixtures, sources: List<SourceRuleOccurrence> = emptyList()) =
        StatementSummary(setOf(x), listOf(MicroEdge.of(starEdge(x, listOf(f.field("field")), ret, emptyList()))),
            emptyList(), emptyMap(), sources = sources)
    private fun markedSummary(actor: RunMethodAnalyzer, premise: InitialAp): List<TaintTree> = actor.summaries.all()
        .filter { it.first == premise && it.second.base == ret }.map { it.second }.filterIsInstance<TaintTree>().toList()

    @Test fun `covered transport still evaluates local CM and keeps only FLOW handoff`() {
        MethodAnalysisFixtures().use { f ->
            val t = MarkSlot.Concrete(f.mark("T"))
            f.statement(1, read(f))
            val sink = localSink(listOf(f.pattern(ret, mark = t)))
            f.exitRules(2, ExitRules(localRules(listOf(sink)), false, emptySet()))
            val actor = fullCore(f)
            val flow = initial(f, MarkSlot.STAR)
            val marked = initial(f, t)
            actor.addInitial(flow)
            actor.addInitial(marked)
            f.drain(actor, quantum = 1)
            assertEquals(1, f.vulnerabilities.witnessesOf(1).count(), "CM must observe the real marked local arrival")
            assertTrue(f.processed.any { it.premise == marked && it.facts is TaintTree })
            assertTrue(markedSummary(actor, marked).isEmpty(), "Pure diagonal output has FLOW guidance")
            assertTrue(actor.summaries.demandEdges().any { it.first == flow && it.second is FlowTree && it.second.base == ret })
            assertTrue(actor.summaries.demandEdges().none { it.first == marked && it.second.base == ret })

            // Invoke the original AP emission/restriction path directly. No StrongQueries owner
            // or concrete-query permission participates in this transport replacement.
            val guide = DemandPattern(f.pattern(ret, tail = Tail.ANY, mark = MarkSlot.STAR), flow.toPattern())
            val actual = f.fact(ret, mark = t)
            val backward = ApMode(false, Direction.BACKWARD, 1)
            val query = f.ops.emit(guide, actual).single()
            assertEquals(MarkSlot.STAR, query.mark)
            val image = CollectingOut()
            f.ops.applyEdge(f.ops.startFact(query), query,
                starEdge(ret, emptyList(), x, listOf(f.field("field"))), false, backward, image)
            val selected = image.results.flatMap { f.ops.restrict(query, it, guide) }
            assertTrue(selected.isNotEmpty())
            val applied = CollectingOut()
            selected.forEach { f.ops.applySummary(actual, query, it, backward, applied) }
            assertTrue(applied.results.flatMap { f.ops.leaves(it).toList() }.any {
                it.fact.base == x && it.fact.path == listOf(f.field("field")) && it.fact.mark == t
            }, "The original abstract guide yields the concrete marked predecessor")
        }
    }

    @Test fun `field sensitive same mark rule keeps the run2 source witness`() {
        DriverFixtures().use { f ->
            val p = f.program
            val main = p.method("protected same T main", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val callee = p.method("protected same T callee", listOf(listOf(1), emptyList()), 1).key()
            val value = AccessPathBase.LocalVar(0)
            val result = AccessPathBase.LocalVar(1)
            val left = p.field("left")
            val right = p.field("right")
            val t = MarkSlot.Concrete(p.mark("T"))
            val producer = PathEdge(ZERO_FACT, PathFact(value, listOf(left), Tail.EXACT, t), ExclusionSet.Empty)
            p.entry(main, RuleStatement(f.summary(ZERO_KEEP, producer), StatementSummary.EMPTY, emptyList()))
            val builder = RulePredicate.Builder(f.cancellation)
            val check = p.pattern(x, listOf(left), mark = t)
            val predicate = builder.build(builder.leaf(check))
            val id = RuleOccurrenceId(FormKey(FormOwner(), callee.method, callee, p.inst(callee, 0)), RuleKind.CALL_SOURCE, 0)
            val action = SourceAction(ActionId(id, ActionRole.SOURCE, 0), p.pattern(ret, tail = Tail.ANY, mark = t).fact)
            val source = SourceRuleOccurrence(id, predicate, listOf(action))
            p.statement(callee, 0, StatementSummary(setOf(x),
                listOf(MicroEdge.of(ZERO_KEEP), MicroEdge.of(starEdge(x, listOf(right), ret, emptyList()))),
                emptyList(), emptyMap(), sources = listOf(source)))
            p.call(main, 1, CallPlan(setOf(value, result), listOf(
                CallStage.Edges(CallPoint.BEFORE, CallPoint.BOUND, StageKind.BIND_IN,
                    f.summary(ZERO_KEEP, starEdge(value, emptyList(), x, emptyList()))),
                CallStage.Actions(CallPoint.BOUND, CallPoint.ADDED, emptyList()),
                CallStage.Callees(CallPoint.ADDED, CallPoint.RETURNED, listOf(callee)),
                CallStage.Actions(CallPoint.RETURNED, CallPoint.REWRITTEN, emptyList()),
                CallStage.Edges(CallPoint.REWRITTEN, CallPoint.AFTER, StageKind.BIND_BACK,
                    f.summary(ZERO_KEEP, starEdge(ret, emptyList(), result, emptyList())))
            ), emptyList(), CallPoint.BEFORE, CallPoint.AFTER))
            val sink = SinkRule(f.rule("protected same T sink"), 0, listOf(p.pattern(result, mark = t)), emptyList())
            p.exit(main, 2, ExitRules(localRules(listOf(sink)), false, emptySet()))
            val report = f.driver(FixedLimits(listOf(1, 1, 2)), run1MarkMode = MarkMode.FULL).analyze(listOf(main))
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertTrue(f.results.any { it.runIndex == 2 && it.status == RunStatus.COMPLETE })
            val run1 = f.results.first()
            val markedGuides = run1.analyzers.single { it.key == callee }.summaries.demandEdges()
                .filter { (it.first as? InitialAp)?.mark == t && it.second.base == ret }.toList()
            assertTrue(markedGuides.isNotEmpty(), "The coarse right FLOW must not erase the left-dependent rule guide")
            assertTrue(markedGuides.all { (it.second as TaintTree).nonSubsumable != null })
            assertTrue(f.results.single { it.runIndex == 2 }.analyzers.any { actor ->
                actor.sourceHits?.occurrences()?.any { it.method == main && it.forward == producer } == true
            }, "Run-2 must retain the concrete left source path")
            assertTrue(report.entries.any { it.key.rule == sink.rule })
        }
    }

    @Test fun `same mark source keeps its marked demand despite parallel FLOW coverage`() {
        MethodAnalysisFixtures().use { f ->
            val t = MarkSlot.Concrete(f.mark("T"))
            val rule = source(f, 1, 0, f.pattern(x, mark = t), f.pattern(ret, tail = Tail.ANY, mark = t).fact)
            f.statement(1, read(f, listOf(rule)))
            val actor = fullCore(f)
            val flow = initial(f, MarkSlot.STAR)
            val marked = initial(f, t)
            actor.addInitial(flow)
            actor.addInitial(marked)
            f.drain(actor, quantum = 1)
            val result = markedSummary(actor, marked).single()
            assertNotNull(result.nonSubsumable)
            assertTrue(actor.summaries.demandEdges().any { it.first == marked && it.second.base == ret })
            assertTrue(actor.summaries.all().any { it.first == flow && it.second.base == ret && it.second is FlowTree })
        }
    }

    @Test fun `local cross mark cycle restores T with a retained protected demand`() {
        MethodAnalysisFixtures(listOf(listOf(1), listOf(2), listOf(3), emptyList()), normalExit = 3).use { f ->
            val t = MarkSlot.Concrete(f.mark("T"))
            val u = MarkSlot.Concrete(f.mark("U"))
            val first = source(f, 1, 0, f.pattern(x, mark = t), f.pattern(z, tail = Tail.ANY, mark = u).fact)
            val second = source(f, 2, 1, f.pattern(z, mark = u), f.pattern(ret, tail = Tail.ANY, mark = t).fact)
            f.statement(1, read(f, listOf(first)))
            f.statement(2, StatementSummary(setOf(z), emptyList(), emptyList(), emptyMap(), sources = listOf(second)))
            val actor = fullCore(f)
            val marked = initial(f, t)
            actor.addInitial(initial(f, MarkSlot.STAR))
            actor.addInitial(marked)
            f.drain(actor, quantum = 1)
            val restored = markedSummary(actor, marked).single()
            assertNotNull(restored.nonSubsumable)
            assertEquals(t.mark, (f.ops.leaves(restored).single().fact.mark as MarkSlot.Concrete).mark)
            assertTrue(actor.summaries.demandEdges().any { it.first == marked && it.second.base == ret })
        }
    }

    @Test fun `late input protection updates accepted rule output without duplicate sink identity`() {
        MethodAnalysisFixtures().use { f ->
            val t = MarkSlot.Concrete(f.mark("T"))
            val u = MarkSlot.Concrete(f.mark("U"))
            val rule = source(f, 1, 0, f.pattern(x, mark = t), f.pattern(ret, tail = Tail.ANY, mark = u).fact)
            f.statement(1, StatementSummary(setOf(x), emptyList(), emptyList(), emptyMap(), sources = listOf(rule)))
            f.exitRules(2, ExitRules(localRules(listOf(localSink(listOf(f.pattern(ret, mark = u))))), false, emptySet()))
            val actor = fullCore(f)
            val marked = initial(f, t)
            actor.addInitial(marked)
            f.drain(actor, quantum = 1)
            assertNull(markedSummary(actor, marked).single().nonSubsumable)
            val reports = f.vulnerabilities.witnessesOf(1).map { it.first }.toSet()
            val input = f.ops.startFact(marked, actor.mode) as TaintTree
            actor.emitAfter(marked, f.inst(0), input.withProtection(input.root))
            f.drain(actor, quantum = 1)
            assertNotNull(markedSummary(actor, marked).single().nonSubsumable)
            assertEquals(reports, f.vulnerabilities.witnessesOf(1).map { it.first }.toSet())
            assertEquals(1, f.vulnerabilities.witnessesOf(1).count())
        }
    }

    @Test fun `canonical callee initials do not inherit caller protection`() {
        MethodAnalysisFixtures().use { f ->
            val t = f.mark("T")
            val actor = fullCore(f)
            val policy = initial(f, MarkSlot.STAR)
            actor.addMarkRequest(policy, t)
            val incoming = f.fact(x, mark = MarkSlot.Concrete(t), layer = Layer.DEMAND) as TaintTree
            f.admit(actor, CallerRef(f.key, f.manager.zero, Layer.DEMAND, f.inst(1)), Layer.DEMAND,
                incoming.withProtection(incoming.root))
            f.drain(actor, quantum = 1)
            val marked = actor.initials.all().filter { it.mark == MarkSlot.Concrete(t) }.toList()
            assertTrue(marked.isNotEmpty(), "The requested concrete input must be analyzed")
            for (premise in marked) {
                val entries = actor.edges.edgesAt(f.inst(0), premise).map { it.second }.filterIsInstance<TaintTree>().toList()
                assertTrue(entries.isNotEmpty())
                assertTrue(entries.all { it.nonSubsumable == null }, "A globally shared hypothesis has no caller flag")
            }
        }
    }

    @Test fun `late contribution protection updates every completed multi-input rule origin`() {
        MethodAnalysisFixtures().use { f ->
            val t = MarkSlot.Concrete(f.mark("T"))
            val u = MarkSlot.Concrete(f.mark("U"))
            val v = MarkSlot.Concrete(f.mark("V"))
            val builder = RulePredicate.Builder(f.cancellation)
            val predicate = builder.build(builder.and(listOf(
                builder.leaf(f.pattern(x, mark = t)), builder.leaf(f.pattern(z, mark = u)))))
            val id = RuleOccurrenceId(FormKey(FormOwner(), f.key.method, f.key, f.inst(1)), RuleKind.CALL_SOURCE, 0)
            val source = SourceRuleOccurrence(id, predicate, listOf(SourceAction(ActionId(id, ActionRole.SOURCE, 0),
                f.pattern(ret, tail = Tail.ANY, mark = v).fact)))
            f.statement(1, StatementSummary(setOf(x, z), emptyList(), emptyList(), emptyMap(), sources = listOf(source)))
            val actor = fullCore(f)
            val first = initial(f, t)
            val second = f.manager.initial(f.pattern(z, tail = Tail.STAR, mark = u))
            actor.addInitial(first)
            actor.addInitial(second)
            f.drain(actor, quantum = 1)
            for (origin in listOf(first, second)) assertNull(markedSummary(actor, origin).single().nonSubsumable)
            val input = f.ops.startFact(first, actor.mode) as TaintTree
            actor.emitAfter(first, f.inst(0), input.withProtection(input.root))
            f.drain(actor, quantum = 1)
            for (origin in listOf(first, second)) {
                assertNotNull(markedSummary(actor, origin).single().nonSubsumable)
                assertTrue(actor.summaries.demandEdges().any { it.first == origin && it.second.base == ret })
            }
            val steps = actor.steps
            actor.emitAfter(first, f.inst(0), input.withProtection(input.root))
            f.drain(actor, quantum = 1)
            assertEquals(steps, actor.steps, "Repeated annotation delivery adds no more work")
        }
    }

    @Test fun `selected cleaner residual carries its protected dependency through a later cut`() {
        MethodAnalysisFixtures(listOf(listOf(1), listOf(2), listOf(3), emptyList()), normalExit = 3).use { f ->
            val t = f.mark("T")
            val cleaner = Cleaner(x, f.manager.path(listOf(f.field("below"))), CleanReach.AT_AND_BELOW, t)
            val plan = CallPlan(setOf(x), listOf(
                CallStage.Actions(CallPoint.RETURNED, CallPoint.REWRITTEN, listOf(CleanStep.Clean(cleaner))),
                CallStage.Edges(CallPoint.REWRITTEN, CallPoint.AFTER, StageKind.BIND_BACK, StatementSummary.identities(listOf(x)))
            ), emptyList(), CallPoint.RETURNED, CallPoint.AFTER)
            f.call(1, plan)
            f.statement(2, StatementSummary(setOf(x), listOf(MicroEdge.of(starEdge(x, emptyList(), ret, emptyList()))),
                emptyList(), emptyMap()))
            val actor = fullCore(f, calls = true)
            val marked = initial(f, MarkSlot.Concrete(t))
            val exact = f.fact(x, mark = MarkSlot.Concrete(t), layer = Layer.DEMAND)
            actor.emitAfter(marked, f.inst(0), exact)
            f.drain(actor, quantum = 1)
            assertNotNull(markedSummary(actor, marked).single().nonSubsumable)
            assertTrue(actor.summaries.demandEdges().any { it.first == marked && it.second.base == ret })
        }
    }

    @Test fun `field cleaner merges equal plain and protected alias images before handoff`() {
        for (bulk in listOf(false, true)) for (plainFirst in listOf(false, true))
        MethodAnalysisFixtures(listOf(listOf(1), listOf(2), listOf(3), emptyList()), normalExit = 3).use { f ->
            val t = f.mark("T")
            val u = f.mark("U")
            val temporary = AccessPathBase.CleanerTemporary()
            val written = AccessPathBase.Argument(2)
            val plainField = f.field("plain")
            val protectedField = f.field("protected")
            val first = f.field("first")
            val second = f.field("second")
            fun summary(vararg edges: PathEdge) = StatementSummary(edges.map { it.from.base }.toSet(),
                edges.map(MicroEdge::of), emptyList(), emptyMap())
            val reads = listOf(starEdge(z, listOf(plainField), temporary, emptyList()),
                starEdge(z, listOf(protectedField), temporary, emptyList()))
            val read = summary(*(if (plainFirst) reads else reads.reversed()).toTypedArray())
            val write = summary(starEdge(temporary, emptyList(), written, listOf(first, second)))
            val field = CleanStep.Field(temporary, read,
                Cleaner(temporary, null, CleanReach.AT_AND_BELOW, if (bulk) f.mark("W") else u), write)
            val raw = listOf(field) + if (bulk) listOf(u, f.mark("V")).map {
                CleanStep.Clean(Cleaner(written, null, CleanReach.AT_AND_BELOW, it))
            } else emptyList()
            val actions = if (bulk) CallStage.Actions.run1FullReturnRewriter(raw, f.manager.marks)
                else CallStage.Actions(CallPoint.RETURNED, CallPoint.REWRITTEN, raw)
            f.call(1, CallPlan(setOf(z, written, temporary), listOf(
                actions,
                CallStage.Edges(CallPoint.REWRITTEN, CallPoint.AFTER, StageKind.BIND_BACK,
                    StatementSummary.identities(listOf(written)))
            ), emptyList(), CallPoint.RETURNED, CallPoint.AFTER))
            f.statement(2, summary(starEdge(written, listOf(first), ret, emptyList())))
            val actor = fullCore(f, calls = true)
            val marked = initial(f, MarkSlot.Concrete(t))
            val protected = f.fact(z, listOf(protectedField), mark = MarkSlot.Concrete(t), layer = Layer.DEMAND) as TaintTree
            val plain = f.fact(z, listOf(plainField), mark = MarkSlot.Concrete(t), layer = Layer.DEMAND) as TaintTree
            val ordinary = if (!bulk) f.manager.taintAlg.mergeAdd(plain.root, protected.root) else {
                // Distinct images first become equal after the compiled U/V cleanup block.
                val extraU = f.fact(z, listOf(plainField), mark = MarkSlot.Concrete(u), layer = Layer.DEMAND) as TaintTree
                val extraV = f.fact(z, listOf(protectedField), mark = MarkSlot.Concrete(f.mark("V")), layer = Layer.DEMAND) as TaintTree
                f.manager.taintAlg.mergeAdd(f.manager.taintAlg.mergeAdd(plain.root, protected.root),
                    f.manager.taintAlg.mergeAdd(extraU.root, extraV.root))
            }
            val packed = f.manager.taintTree(z, Layer.DEMAND,
                ordinary, nonSubsumable = protected.root)
            actor.emitAfter(initial(f, MarkSlot.STAR), f.inst(0), f.fact(ret, tail = Tail.ANY,
                mark = MarkSlot.STAR, layer = Layer.DEMAND))
            actor.emitAfter(marked, f.inst(0), packed)
            f.drain(actor, quantum = 1)
            val result = markedSummary(actor, marked)
            assertTrue(result.isNotEmpty(), "Alias-result deduplication must retain the protected marked guide")
            assertTrue(result.all { it.nonSubsumable != null })
            assertTrue(actor.summaries.demandEdges().any { it.first == marked && it.second.base == ret })
        }
    }
}
