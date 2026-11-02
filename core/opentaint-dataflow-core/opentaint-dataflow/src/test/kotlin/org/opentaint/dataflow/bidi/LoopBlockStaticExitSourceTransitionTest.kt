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
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** The real driver must preserve the static exit-source relation through both handoffs. */
class LoopBlockStaticExitSourceTransitionTest {
    @Test fun `operation local static exit source guides backward and the next forward finding`() {
        DriverFixtures().use { f ->
            val p = f.program
            // main: a=srcT(); C.f=a; b=copyInLoops(); sinkU(b);
            // copyInLoops: while (outer()) { while (inner()) { x=C.f; C.g=x; } }
            // EXIT_SOURCE on copyInLoops: CM(C.g,T) -> assign U to ret.$.
            val root = p.method("static exit source root", listOf(
                listOf(1), listOf(2), listOf(3), listOf(4), listOf(5), emptyList(), emptyList()),
                normalExit = 5, exceptionalExit = 6, backwardExitDiscovery = true).key()
            val producer = p.method("static exit source srcT", listOf(listOf(1), listOf(2), emptyList(), emptyList()),
                normalExit = 2, exceptionalExit = 3, backwardExitDiscovery = true).key()
            val copy = p.method("static exit source nested copy", listOf(
                listOf(1), listOf(2, 7), listOf(3, 6), listOf(4), listOf(5),
                listOf(2, 6), listOf(1, 7), emptyList(), emptyList()),
                normalExit = 7, exceptionalExit = 8, backwardExitDiscovery = true).key()
            val a = AccessPathBase.LocalVar(0)
            val b = AccessPathBase.LocalVar(1)
            val x = AccessPathBase.LocalVar(2)
            val returned = AccessPathBase.Return
            val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
            val cf = listOf(cls, p.field("f"))
            val cg = listOf(cls, p.field("g"))
            val t = p.mark("T")
            val u = p.mark("U")
            val tm = MarkSlot.Concrete(t)
            val um = MarkSlot.Concrete(u)
            val sourceT = PathEdge(ZERO_FACT, PathFact(returned, emptyList(), Tail.EXACT, tm), ExclusionSet.Empty)
            p.entry(producer, RuleStatement(f.summary(ZERO_KEEP, sourceT), StatementSummary.EMPTY, emptyList()))

            fun call(callee: MethodKey, output: AccessPathBase): CallPlan = CallPlan(setOf(STATIC, output), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP, keepEdge(STATIC))),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Callees(ADDED, RETURNED, listOf(callee)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP, keepEdge(STATIC),
                    starEdge(returned, emptyList(), output, emptyList()))),
            ), emptyList(), BEFORE, AFTER)
            p.call(root, 1, call(producer, a))
            val seedWrite = starEdge(a, emptyList(), STATIC, cf)
            p.staticWrite(root, 2, Pattern(seedWrite.to, ExclusionSet.Empty), seedWrite,
                MicroEdgeBuilder().apply {
                    keepZero()
                    this.write(STATIC, cf, weak = false, values = listOf(a), aliasPaths = emptyList())
                }.build())
            p.call(root, 3, call(copy, b))

            val read = starEdge(STATIC, cf, x, emptyList())
            // Use the ordinary instruction lowering: reads keep their source,
            // and writes keep proper prefixes while replacing their target.
            p.staticRead(copy, 3, read, MicroEdgeBuilder().apply { keepZero(); this.read(x, STATIC, cf) }.build())
            val write = starEdge(x, emptyList(), STATIC, cg)
            p.staticWrite(copy, 4, Pattern(write.to, ExclusionSet.Empty), write,
                MicroEdgeBuilder().apply {
                    keepZero()
                    this.write(STATIC, cg, weak = false, values = listOf(x), aliasPaths = emptyList())
                }.build())
            val form = FormKey(FormOwner(), copy.method, copy, p.inst(copy, 7))
            val occurrence = RuleOccurrenceId(form, RuleKind.EXIT_SOURCE, 0)
            val action = SourceAction(ActionId(occurrence, ActionRole.SOURCE, 0),
                p.pattern(returned, mark = um).fact)
            val condition = p.pattern(STATIC, cg, Tail.EXACT, tm)
            val builder = RulePredicate.Builder(f.cancellation, f.manager.marks)
            val exitSource = SourceRuleOccurrence(occurrence, builder.build(builder.leaf(condition)), listOf(action))
            val sourceU = exitSource.transfer(condition, action).forward
            // JIRRuleForms.source registers markInputs(predicate, occurrence).
            // JIRBoundaryForms.exitRules also keeps ZERO and each predicate base.
            // Omitting MarkInput would test an incomplete provider form: only
            // the operation-local write shortcut could then evaluate this rule.
            val exitSourceSummary = MicroEdgeBuilder().apply {
                keepZero()
                keep(STATIC)
                source(exitSource)
                staticOperation(StaticOperation.MarkInput(OperationId(form,
                    action = ActionId(occurrence, ActionRole.MARK_INPUT, 0)), condition))
            }.build()
            p.exit(copy, 7, ExitRules(RuleStatement(exitSourceSummary, StatementSummary.EMPTY, emptyList()),
                false, emptySet()))

            val sink = SinkRule(f.rule("static exit source caller sink U"), 0,
                listOf(p.pattern(b, mark = um)), emptyList())
            val identity = f.summary(ZERO_KEEP, keepEdge(b))
            p.call(root, 4, CallPlan(setOf(b), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, identity),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED, identity),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, identity),
            ), listOf(sink), BEFORE, AFTER))

            val driver = f.driver(FixedLimits(listOf(1, 1, 2, 3)), 20.seconds, run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(root))
            if (report.entries.none { it.descriptor.key.ruleId == sink.rule.id }) println(buildString {
                fun image(original: PremiseKey, value: Facts): String =
                    "${original.members.map { it.toPattern() }} -> ${f.ops.leaves(value).toList()} layer=${value.layer}"
                appendLine("STATIC_EXIT_SOURCE_TRANSITION end=${report.end}")
                for (config in f.configs) appendLine("config=${config.index} Upermission=${config.seeds.allowsSource(copy, p.inst(copy, 7), sourceU, action.id)}")
                for (frontier in driver.frontiers) appendLine("frontier=${frontier.run} demands=${frontier.demandEdges} targets=${frontier.targetDemand} reports=${frontier.reportedSinks}")
                for (result in f.results) for (actor in result.analyzers) {
                    appendLine("run=${result.runIndex} method=${actor.key.method.name} targets=${actor.targets} sources=${actor.sourceHits?.occurrences()?.toList()}")
                    for ((original, value) in actor.summaries.all()) appendLine("ROOT ${image(original, value)}")
                    for (block in actor.blockSummaries()) for ((original, value) in block.summaries.all())
                        appendLine("BLOCK ${block.key} ${image(original, value)}")
                }
                for (row in f.processed) appendLine("processed=${row.run} method=${row.method.method.name} at=${row.delta.node.location.index} ${image(row.delta.premise, row.delta.facts)}")
            })
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertTrue(f.results.all { it.status == RunStatus.COMPLETE })
            assertTrue(f.configs.all { it.mode.markMode == MarkMode.FULL })
            assertEquals(listOf(1, 1, 2), f.configs.take(3).map { it.fieldLimit })
            assertEquals(0, driver.frontiers.first().reportedSinks, "The run-1 static DEMAND is not a normal report")

            val firstCopy = f.results.single { it.runIndex == 1 }.analyzers.single { it.key == copy }
            fun containsExitU(value: Facts): Boolean = f.ops.leaves(value).any {
                it.fact.base == returned && it.fact.mark == um
            }
            assertTrue(firstCopy.summaries.all().any { (original, value) ->
                original.members.any { it.base == STATIC && it.pathData.toList() == cf && it.mark == tm } &&
                    value.layer == Layer.DEMAND && containsExitU(value)
            }, "The genuine initial run must produce C.f/T -> ret/U without manual replay")
            val localSources = firstCopy.blockSummaries().filter { block ->
                block.key.scope.entry == PortId.ROOT_EXIT && block.summaries.all().any { (original, value) ->
                    original.members.any { it.base == STATIC && it.pathData.toList() == cg && it.mark == tm } &&
                        value.layer == Layer.DEMAND && containsExitU(value)
                }
            }.toList()
            assertTrue(localSources.isNotEmpty(), "The original exit source owns actual ROOT_EXIT operation-local rows")
            val layout = f.shared.contexts.blockLayout(copy)
            val ordinarySources = firstCopy.blockSummaries().filter { block ->
                block.key.scope.block == layout.ownerOf(7) && layout.normalExit(block.key.scope.entry) != null &&
                    block.summaries.all().any { (original, value) ->
                        original.members.any { it.base == STATIC && it.pathData.toList() == cg && it.mark == tm } &&
                            value.layer == Layer.DEMAND && containsExitU(value)
                    }
            }.toList()
            assertTrue(ordinarySources.isNotEmpty(),
                "The actual MarkInput must also produce a source row in the ordinary AL/J invocation")
            val backward = f.configs.single { it.index == 2 }
            val demand = checkNotNull(backward.demand)
            val retU = f.manager.factsOf(p.pattern(returned, mark = um).fact, ExclusionSet.Empty, Layer.NORMAL)
            for (local in localSources + ordinarySources) {
                val reverseScope = BlockScope(local.key.scope.block, local.key.exit)
                assertTrue(demand.scope(copy, reverseScope).initials(retU, backward.admissionPolicy).any {
                    it.initial.base == returned && it.initial.mark == um
                }, "The genuine scoped source row must give run-2 a local ret/U initial")
            }
            val cgT = f.manager.factsOf(p.pattern(STATIC, cg, Tail.EXACT, tm).fact, ExclusionSet.Empty, Layer.DEMAND)
            for (local in ordinarySources) {
                val reverseScope = BlockScope(local.key.scope.block, local.key.exit)
                val view = demand.scope(copy, reverseScope)
                val initial = view.initials(retU, backward.admissionPolicy).first {
                    it.initial.base == returned && it.initial.mark == um
                }
                assertTrue(view.intersect(local.key.scope.entry, initial.initial, cgT, backward.admissionPolicy).isNotEmpty(),
                    "Run-2 source output must use the complete ret/U -> C.g/T pair at the ordinary J exit")
            }
            val backwardCopy = f.results.single { it.runIndex == 2 }.analyzers.single { it.key == copy }
            assertTrue(checkNotNull(backwardCopy.sourceHits).occurrences().any {
                it.method == copy && it.statement == p.inst(copy, 7) && it.forward == sourceU && it.action == action.id
            }, "Run-2 must execute the original physical EXIT_SOURCE and record its exact action")
            assertTrue(f.configs.single { it.index == 3 }.seeds.allowsSource(copy, p.inst(copy, 7), sourceU, action.id))
            val forwardRoot = f.results.single { it.runIndex == 3 }.analyzers.single { it.key == root }
            assertTrue(forwardRoot.targets.any { row -> row.premise.isZero &&
                (row.target as? Target.NormalTarget)?.let { f.shared.reportCatalog.descriptor(it.id).key.ruleId == sink.rule.id } == true
            }, "The next forward iteration must derive a NORMAL root report through the caller")
            assertEquals(listOf(sink.rule.id), report.entries.map { it.descriptor.key.ruleId })
            assertEquals(p.inst(root, 4), report.entries.single().descriptor.key.statement)
            assertTrue(f.results.flatMap { it.analyzers }.all { it.key in setOf(root, producer, copy) })
        }
    }
}
