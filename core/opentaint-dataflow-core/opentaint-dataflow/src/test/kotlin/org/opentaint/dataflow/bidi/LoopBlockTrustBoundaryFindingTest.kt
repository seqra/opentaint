package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** A request binding and a data mark meet a separately bound session receiver. */
class LoopBlockTrustBoundaryFindingTest {
    private fun run(withLoop: Boolean, exactArray: Boolean = false, conditionalSession: Boolean = true) {
        DriverFixtures().use { f ->
            val p = f.program
            // ENTRY metadata: request/$REQ.
            // cookies=request.getCookies(); // CM(this,$REQ) -> ret.[any-taint]/DATA.
            // while (again()) { param=cookies[i]; if (match()) break; }
            // session=request.getSession(); // CM(this,$REQ) -> ret.$/SESSION.
            // session.setAttribute(param,"value"); // CM(this,SESSION) AND CM(arg0,DATA).
            val method = p.method("trust boundary loop=$withLoop", listOf(
                listOf(1), listOf(2), listOf(3, 6), listOf(4), listOf(5),
                if (withLoop) listOf(2, 6) else listOf(6), listOf(7), listOf(8), emptyList(), emptyList()),
                normalExit = 8, exceptionalExit = 9, backwardExitDiscovery = true).key()
            val request = AccessPathBase.Argument(0)
            val cookies = AccessPathBase.LocalVar(0)
            val param = AccessPathBase.LocalVar(1)
            val session = AccessPathBase.LocalVar(2)
            val cookie = AccessPathBase.LocalVar(3)
            val receiver = AccessPathBase.This
            val returned = AccessPathBase.Return
            val sinkArg = AccessPathBase.Argument(1)
            val req = MarkSlot.Concrete(p.mark("T"))
            val data = MarkSlot.Concrete(p.mark("U"))
            val boundSession = MarkSlot.Concrete(p.mark("V"))
            val element = f.manager.accessors.index(ElementAccessor)
            val owner = FormOwner()
            fun occurrence(at: Int, kind: RuleKind) = RuleOccurrenceId(
                FormKey(owner, method.method, method, p.inst(method, at)), kind, 0)
            val entryId = occurrence(0, RuleKind.ENTRY_SOURCE)
            val entryAction = ActionId(entryId, ActionRole.SOURCE, 0)
            val entryEdge = PathEdge(ZERO_FACT, p.pattern(request, mark = req).fact, ExclusionSet.Empty)
            p.entry(method, RuleStatement(MicroEdgeBuilder().apply {
                keepZero(); sourceEdge(entryEdge, entryAction)
            }.build(), StatementSummary.EMPTY, emptyList()))

            fun sourceCall(at: Int, output: AccessPathBase, targets: List<PathFact>,
                           conditional: Boolean = true): List<Pair<PathEdge, ActionId>> {
                val condition = p.pattern(receiver, mark = req)
                val builder = RulePredicate.Builder(f.cancellation, f.manager.marks)
                val id = occurrence(at, RuleKind.CALL_SOURCE)
                val actions = targets.mapIndexed { index, target -> SourceAction(ActionId(id, ActionRole.SOURCE, index), target) }
                val source = if (conditional) SourceRuleOccurrence(id, builder.build(builder.leaf(condition)), actions) else null
                val transfers = actions.map { action ->
                    (source?.transfer(condition, action)?.forward
                        ?: PathEdge(ZERO_FACT, action.target, ExclusionSet.Empty)) to action.id
                }
                // JIRCallPlanBuilder's source branch bypasses return cleanup;
                // ordinary receiver identity is a separate unresolved branch.
                val sources = MicroEdgeBuilder().apply {
                    keepZero()
                    if (source != null) source(source)
                    else transfers.forEach { (edge, action) -> sourceEdge(edge, action) }
                }.buildStage()
                p.call(method, at, CallPlan(setOf(request, output), listOf(
                    CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP,
                        starEdge(request, emptyList(), receiver, emptyList()))),
                    CallStage.Edges(BOUND, REWRITTEN, SOURCES, sources),
                    CallStage.Actions(BOUND, ADDED, emptyList()),
                    CallStage.Edges(ADDED, RETURNED, UNRESOLVED, f.summary(ZERO_KEEP, keepEdge(receiver))),
                    CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                    CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP,
                        starEdge(receiver, emptyList(), request, emptyList()),
                        starEdge(returned, emptyList(), output, emptyList()))),
                ), emptyList(), BEFORE, AFTER))
                return transfers
            }
            // resolveWithArray expands BaseOnly array-result assignment to root
            // and element EXACT actions. It does not imply a MUST source.
            val cookieTargets = if (exactArray) listOf(
                p.pattern(returned, mark = data).fact,
                p.pattern(returned, listOf(element), mark = data).fact,
            ) else listOf(p.pattern(returned, tail = Tail.ANY_TAINT, mark = data).fact)
            val cookieSources = sourceCall(1, cookies, cookieTargets)
            p.statement(method, 3, MicroEdgeBuilder().apply { read(cookie, cookies, listOf(element)) }.build())
            // The ordinary get-value model is CopyAllMarks(This,Result), from
            // JIRMethodGetDefault.defaultPropagationRules + JIRRuleForms.pass.
            p.call(method, 4, CallPlan(setOf(cookie, param), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP,
                    starEdge(cookie, emptyList(), receiver, emptyList()))),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED, f.summary(ZERO_KEEP, keepEdge(receiver),
                    starEdge(receiver, emptyList(), returned, emptyList()))),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP,
                    starEdge(receiver, emptyList(), cookie, emptyList()),
                    starEdge(returned, emptyList(), param, emptyList()))),
            ), emptyList(), BEFORE, AFTER))
            // The first getSession step belongs to the independent SINK pattern
            // automaton. Its generated receiver marker is an unconditional
            // typed ZERO source; it need not check the SOURCE automaton's REQ.
            val sessionSources = sourceCall(6, session,
                listOf(p.pattern(returned, mark = boundSession).fact), conditionalSession)
            val sinkBuilder = RulePredicate.Builder(f.cancellation, f.manager.marks)
            val predicate = sinkBuilder.build(sinkBuilder.and(listOf(
                sinkBuilder.leaf(p.pattern(receiver, mark = boundSession)),
                sinkBuilder.leaf(p.pattern(sinkArg, mark = data)),
            )))
            val sink = SinkRule(f.rule("trust boundary receiver and value"), 0, predicate.leaves,
                emptyList(), occurrence(7, RuleKind.CALL_SINK), predicate)
            val bound = f.summary(ZERO_KEEP, keepEdge(receiver), keepEdge(sinkArg))
            p.call(method, 7, CallPlan(setOf(session, param), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP,
                    starEdge(session, emptyList(), receiver, emptyList()),
                    starEdge(param, emptyList(), sinkArg, emptyList()))),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED, bound),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP,
                    starEdge(receiver, emptyList(), session, emptyList()),
                    starEdge(sinkArg, emptyList(), param, emptyList()))),
            ), listOf(sink), BEFORE, AFTER))
            val driver = f.driver(FixedLimits(listOf(1, 1, 2, 3, 4)), 20.seconds, run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(method))
            if (report.entries.none { it.descriptor.key.ruleId == sink.rule.id }) println(buildString {
                fun image(original: PremiseKey, value: Facts) =
                    "${original.members.map { it.toPattern() }} -> ${f.ops.leaves(value).toList()} layer=${value.layer}"
                appendLine("TRUST_BOUNDARY_TRACE loop=$withLoop exactArray=$exactArray conditionalSession=$conditionalSession end=${report.end}")
                for (config in f.configs) appendLine("config=${config.index} entryPermission=${config.seeds.allowsSource(method,p.inst(method,0),entryEdge,entryAction)} cookiePermissions=${cookieSources.map { config.seeds.allowsSource(method,p.inst(method,1),it.first,it.second) }} sessionPermissions=${sessionSources.map { config.seeds.allowsSource(method,p.inst(method,6),it.first,it.second) }}")
                for (frontier in driver.frontiers) appendLine("frontier=${frontier.run} demand=${frontier.demandEdges} targetDemand=${frontier.targetDemand} reports=${frontier.reportedSinks}")
                if (withLoop) {
                    val layout = f.shared.contexts.blockLayout(method)
                    val after = checkNotNull(layout[layout.root].after)
                    val first = f.results.first { it.runIndex == 1 }.analyzers.single { it.key == method }
                    val scopes = first.blockSummaries().filter { it.key.scope.block == after }.map { it.key.scope }.distinct().toList()
                    val dataInput = f.manager.factsOf(p.pattern(param, mark = data).fact, ExclusionSet.Empty, Layer.NORMAL)
                    for (config in f.configs.filter { it.index >= 3 && it.direction == Direction.FORWARD }) for (scope in scopes) {
                        val view = checkNotNull(config.demand).scope(method, scope)
                        appendLine("C2 run=${config.index} scope=$scope ZERO=${view.initials(Reach.NORMAL, config.admissionPolicy)} DATA=${view.initials(dataInput, config.admissionPolicy).map { it.initial.toPattern() to it.layer }}")
                        val saved = f.records.byEntry(method, scope, f.manager.zero.toPattern()).filter { record ->
                            record.direction == Direction.FORWARD && record.premise.isZero && f.ops.leaves(record.conclusion).any {
                                it.fact.base == session && it.fact.mark == boundSession
                            }
                        }.toList()
                        appendLine("SAVED_SESSION scope=$scope rows=${saved.map { image(it.premise,it.conclusion) }}")
                    }
                }
                for (result in f.results) for (actor in result.analyzers) {
                    appendLine("run=${result.runIndex} ROOT targets=${actor.targets} sourceHits=${actor.sourceHits?.occurrences()?.toList()}")
                    for ((original, value) in actor.summaries.all()) appendLine("run=${result.runIndex} ROOT ${image(original,value)}")
                    for (block in actor.blockSummaries()) for ((original,value) in block.summaries.all())
                        appendLine("run=${result.runIndex} BLOCK=${block.key} ${image(original,value)}")
                    for (block in actor.blockTargets()) for (row in block.rows)
                        appendLine("run=${result.runIndex} TARGET scope=${block.scope} original=${row.premise.members.map { it.toPattern() }} target=${row.target}")
                    for (block in actor.blockOutgoingTargets()) for (row in block.rows)
                        appendLine("run=${result.runIndex} OUT_TARGET scope=${block.scope} original=${row.premise.members.map { it.toPattern() }} target=${row.target}")
                }
                for (row in f.processed) appendLine("run=${row.run} at=${row.delta.node.location.index} ${image(row.delta.premise,row.delta.facts)}")
            })
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertEquals(listOf(sink.rule.id), report.entries.map { it.descriptor.key.ruleId }, "end=${report.end}")
            assertEquals(p.inst(method,7), report.entries.single().descriptor.key.statement)
            assertTrue(f.results.flatMap { it.analyzers }.all { it.key == method })
        }
    }

    @Test fun `request binding and session receiver meet cookie data after a real loop`() = run(true)
    @Test fun `same metadata source and joined sink report without feedback`() = run(false)
    @Test fun `exact array source and independent ZERO session binding reach joined sink after a loop`() =
        run(true, exactArray = true, conditionalSession = false)
    @Test fun `same exact array and independent session rules reach joined sink without feedback`() =
        run(false, exactArray = true, conditionalSession = false)
}
