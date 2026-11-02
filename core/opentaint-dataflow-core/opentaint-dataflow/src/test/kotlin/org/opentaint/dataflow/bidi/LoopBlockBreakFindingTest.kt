package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Small data-escape controls for OWASP's cookie loop followed by a sink. */
class LoopBlockBreakFindingTest {
    private fun run(sourceTail: Tail) {
        DriverFixtures().use { f ->
            val p = f.program
            // x=source(); while (again()) { param=x; if (match()) break; }
            // sinkT(param); return;
            val method = p.method("loop break $sourceTail", listOf(
                listOf(1), listOf(2, 4), listOf(3), listOf(1, 4), listOf(5), emptyList(), emptyList()),
                normalExit = 5, exceptionalExit = 6, backwardExitDiscovery = true).key()
            val x = AccessPathBase.LocalVar(0)
            val param = AccessPathBase.LocalVar(1)
            val mark = MarkSlot.Concrete(p.mark("T"))
            val source = PathEdge(ZERO_FACT, PathFact(x, emptyList(), sourceTail, mark), ExclusionSet.Empty)
            p.entry(method, RuleStatement(f.summary(ZERO_KEEP, source), StatementSummary.EMPTY, emptyList()))
            p.statement(method, 2, MicroEdgeBuilder().apply { move(param, x) }.build())
            val sink = SinkRule(f.rule("break sink $sourceTail"), 0, listOf(p.pattern(param, mark = mark)), emptyList())
            val keep = f.summary(ZERO_KEEP, keepEdge(param))
            p.call(method, 4, CallPlan(setOf(param), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, keep),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED, keep),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, keep),
            ), listOf(sink), BEFORE, AFTER))
            val report = f.driver(FixedLimits(listOf(1, 1, 2, 3, 4)), 15.seconds,
                run1MarkMode = MarkMode.FULL).analyze(listOf(method))
            if (report.entries.none { it.descriptor.key.ruleId == sink.rule.id }) println(buildString {
                appendLine("BREAK_TRACE tail=$sourceTail end=${report.end}")
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
            assertEquals(listOf(sink.rule.id), report.entries.map { it.descriptor.key.ruleId }, "end=${report.end}")
        }
    }

    @Test fun `normal exact source escapes a loop break into a flat after region`() = run(Tail.EXACT)
    @Test fun `normal uniform source escapes a loop break through refined saved replay`() = run(Tail.ANY_TAINT)

    private fun cookieArray(readValueField: Boolean, withLoop: Boolean = true, ordinaryField: Boolean = false, deepSource: Boolean = false) {
        DriverFixtures().use { f ->
            val p = f.program
            // Source: request has T on the whole object.
            // cookies = request.getCookies();
            // while (again()) { cookie=cookies[i]; value=cookie.getValue();
            //                   param=decode(value); if (match()) break; }
            // sinkT(param);
            val method = p.method("cookie array break $readValueField loop=$withLoop ordinary=$ordinaryField deep=$deepSource", listOf(
                listOf(1), listOf(2), listOf(3, 7), listOf(4), listOf(5), listOf(6),
                if (withLoop) listOf(2, 7) else listOf(7), listOf(8), emptyList(), emptyList()),
                normalExit = 8, exceptionalExit = 9, backwardExitDiscovery = true).key()
            val request = AccessPathBase.Argument(0)
            val cookies = AccessPathBase.LocalVar(0)
            val cookie = AccessPathBase.LocalVar(1)
            val value = AccessPathBase.LocalVar(2)
            val param = AccessPathBase.LocalVar(3)
            val element = if (ordinaryField) p.field("f") else f.manager.accessors.index(ElementAccessor)
            val valueField = p.field("value")
            val mark = MarkSlot.Concrete(p.mark("T"))
            val source = PathEdge(ZERO_FACT, PathFact(request, if (deepSource) listOf(element, valueField) else emptyList(), Tail.ANY_TAINT, mark), ExclusionSet.Empty)
            p.entry(method, RuleStatement(f.summary(ZERO_KEEP, source), StatementSummary.EMPTY, emptyList()))
            fun pass(at: Int, from: AccessPathBase, to: AccessPathBase) {
                val keep = f.summary(ZERO_KEEP, keepEdge(from), keepEdge(to))
                p.call(method, at, CallPlan(setOf(from, to), listOf(
                    CallStage.Edges(BEFORE, BOUND, BIND_IN, keep),
                    CallStage.Actions(BOUND, ADDED, emptyList()),
                    CallStage.Edges(ADDED, RETURNED, UNRESOLVED,
                        f.summary(ZERO_KEEP, keepEdge(from), starEdge(from, emptyList(), to, emptyList()))),
                    CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                    CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, keep),
                ), emptyList(), BEFORE, AFTER))
            }
            pass(1, request, cookies)
            p.statement(method, 3, MicroEdgeBuilder().apply { read(cookie, cookies, listOf(element)) }.build())
            if (readValueField) p.statement(method, 4, MicroEdgeBuilder().apply { read(value, cookie, listOf(valueField)) }.build())
            else pass(4, cookie, value)
            pass(5, value, param)
            val sink = SinkRule(f.rule("cookie break sink $readValueField"), 0, listOf(p.pattern(param, mark = mark)), emptyList())
            val keep = f.summary(ZERO_KEEP, keepEdge(param))
            p.call(method, 7, CallPlan(setOf(param), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, keep),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED, keep),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, keep),
            ), listOf(sink), BEFORE, AFTER))
            val report = f.driver(FixedLimits(listOf(1, 1, 2, 3, 4)), 15.seconds,
                run1MarkMode = MarkMode.FULL).analyze(listOf(method))
            if (report.entries.isEmpty()) println(buildString {
                appendLine("COOKIE_BREAK_TRACE namedValue=$readValueField loop=$withLoop ordinary=$ordinaryField deep=$deepSource end=${report.end}")
                for (config in f.configs) appendLine("config=${config.index} sourcePermission=${config.seeds.allowsSource(method, p.inst(method,0),source)}")
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
            if (withLoop && !deepSource) {
                val layout = f.shared.contexts.blockLayout(method)
                val before = checkNotNull(layout[layout.root].before)
                val first = f.results.single { it.runIndex == 1 }.analyzers.single { it.key == method }
                val prefixes = first.blockSummaries().filter {
                    it.key.scope.block == before && it.key.scope.entry == PortId.ROOT_ENTRY
                }.toList()
                assertTrue(prefixes.any { block -> block.summaries.all().any { (original, facts) ->
                    original.isZero && facts.layer == Layer.NORMAL && f.ops.leaves(facts).any {
                        it.fact.base == cookies && it.fact.path.isEmpty() &&
                            it.fact.tail == Tail.ANY_TAINT && it.fact.mark == mark
                    }
                } }, "The saved before-region span must start before the real entry source, with ZERO as its true original")
                assertTrue(prefixes.any { block ->
                    f.records.byEntry(method, block.key.scope, f.manager.zero.toPattern()).any { record ->
                        record.direction == Direction.FORWARD && record.premise.isZero &&
                            f.ops.leaves(record.conclusion).any {
                                it.fact.base == cookies && it.fact.mark == mark && it.fact.tail == Tail.ANY_TAINT
                            }
                    }
                }, "The genuine NORMAL source prefix must use ordinary scoped native persistence")
                for (result in f.results.filter { it.direction == Direction.BACKWARD })
                    for (actor in result.analyzers) for (hit in actor.sourceHits?.occurrences().orEmpty()) {
                        assertTrue(f.processed.any {
                            it.run == result.runIndex && it.method == method &&
                                it.delta.node == hit.statement
                        }, "A hypothetical saved-prefix probe must not synthesize a physical source hit")
                    }
            }
            assertEquals(listOf(sink.rule.id), report.entries.map { it.descriptor.key.ruleId }, "end=${report.end}")
            if (!withLoop && !deepSource) assertEquals(1, report.end.run, "Removing only the feedback edge needs no AP refinement")
        }
    }

    @Test fun `uniform request reaches array element then breaks to a flat after sink`() = cookieArray(false)
    @Test fun `uniform request reaches array element and named value then breaks to a flat after sink`() = cookieArray(true)

    @Test fun `same uniform request and array transfer reaches sink when only feedback is removed`() = cookieArray(false, withLoop = false)
    @Test fun `same uniform request array and value transfer reaches sink when only feedback is removed`() = cookieArray(true, withLoop = false)

    @Test fun `uniform request reaches ordinary field then breaks to a flat after sink`() = cookieArray(false, ordinaryField = true)

    @Test fun `deep entry source with array and value survives boundary inclusive prefix guidance`() = cookieArray(true, deepSource = true)
    @Test fun `deep entry source with array and value reaches sink without feedback`() = cookieArray(true, withLoop = false, deepSource = true)

    @Test fun `existing concrete MAY admission accepts an equal MAY carrier without NORMAL promotion`() {
        DriverFixtures().use { f ->
            val p = f.program
            val method = p.method("same MAY boundary guide", listOf(listOf(1), emptyList()), normalExit = 1).key()
            val cookies = AccessPathBase.LocalVar(0)
            val element = f.manager.accessors.index(ElementAccessor)
            val mark = MarkSlot.Concrete(p.mark("T"))
            val selected = p.pattern(cookies, listOf(element), Tail.ANY, mark)
            val policy = RestrictedInitialPolicy(2, 1, Direction.BACKWARD, f.manager.marks)
            val demand = org.opentaint.dataflow.bidi.store.DemandStore.Builder(f.manager).apply {
                add(method, DemandPattern(selected, f.manager.zero.toPattern()))
            }.build()
            val actual = f.manager.factsOf(selected.fact, ExclusionSet.Empty, Layer.DEMAND)
            val admitted = demand.initials(method, actual, policy).single()
            assertEquals(selected, admitted.initial.toPattern())
            assertEquals(Layer.DEMAND, admitted.layer)
            assertTrue(demand.acceptsTarget(method, admitted.initial, policy),
                "The existing complete MAY-to-ZERO pair also permits its terminal result")
        }
    }

}
