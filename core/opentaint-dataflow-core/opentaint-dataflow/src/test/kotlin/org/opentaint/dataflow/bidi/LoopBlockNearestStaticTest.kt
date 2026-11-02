package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import kotlin.test.*

class LoopBlockNearestStaticTest {
    @Test fun `static copy keeps nearest and ancestor rows before the real exit rule and root erasure`() {
        // An external writer supplies C.f/T.
        // while (outer()) {
        //   while (inner()) { x=C.f; C.g=x; }
        // }
        // Real normal-exit source rule: CM(C.g,T) assigns U to ret.$.
        val graph = listOf(listOf(1), listOf(2, 7), listOf(3, 6), listOf(4),
            listOf(5), listOf(2, 6), listOf(1, 7), emptyList(), emptyList())
        MethodAnalysisFixtures(graph, normalExit = 7, exceptionalExit = 8).use { f ->
            val x = AccessPathBase.LocalVar(0)
            val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
            val from = listOf(cls, f.field("f"))
            val to = listOf(cls, f.field("g"))
            val t = f.mark("T")
            val u = f.mark("U")
            val read = starEdge(STATIC, from, x, emptyList())
            val readId = OperationId(FormKey(FormOwner(), f.key.method, f.key, f.inst(3)))
            f.statement(3, MicroEdgeBuilder().apply {
                keepZero(); edge(read)
                staticOperation(StaticOperation.Read(readId, read))
            }.buildStage())
            val write = starEdge(x, emptyList(), STATIC, to)
            val writeId = OperationId(FormKey(FormOwner(), f.key.method, f.key, f.inst(4)))
            f.statement(4, MicroEdgeBuilder().apply {
                keepZero(); edge(write)
                staticOperation(StaticOperation.Write(writeId, Pattern(write.to, ExclusionSet.Empty), write))
            }.buildStage())
            val form = FormKey(FormOwner(), f.key.method, f.key, f.inst(7))
            val occurrence = RuleOccurrenceId(form, RuleKind.EXIT_SOURCE, 0)
            val action = ActionId(occurrence, ActionRole.SOURCE, 0)
            val condition = f.pattern(STATIC, to, Tail.EXACT, MarkSlot.Concrete(t))
            val builder = RulePredicate.Builder(f.cancellation, f.manager.marks)
            val predicate = builder.build(builder.leaf(condition))
            val target = f.pattern(AccessPathBase.Return, mark = MarkSlot.Concrete(u))
            val source = SourceRuleOccurrence(occurrence, predicate, listOf(SourceAction(action, target.fact)))
            f.exitRules(7, ExitRules(RuleStatement(StatementSummary(setOf(STATIC), emptyList(),
                emptyList(), emptyMap(), sources = listOf(source)), StatementSummary.EMPTY, emptyList()),
                false, emptySet()))

            val actor = f.core(RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key),
                run1MarkMode = MarkMode.FULL), localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            val service = assertNotNull(actor.runnerPort.staticService)
            val region = f.pattern(STATIC, from, Tail.STAR, MarkSlot.STAR)
            assertTrue(service.commit(StaticBatch().apply {
                writes += region
                supplies += RegionGroups(region, MarkSet.of(t))
            }).isEmpty())
            actor.addRootZero()
            f.drain(actor, quantum = 1)
            val runtime = assertNotNull(actor.blockRuntime)
            val layout = runtime.layout
            val nearest = layout.ownerOf(4)
            assertTrue(layout[nearest].isLoop)
            val ancestor = checkNotNull(layout[nearest].parent)
            assertNotEquals(layout.root, ancestor, "The fixture must exercise an internal ancestor")
            val writerRows = service.statistics().writerRows
            assertTrue(writerRows > 0, "The test must execute the real physical write")
            val hasExitDependency = actor.summaries.all().any { (original, facts) ->
                original.members.any {
                    it.base == STATIC && it.pathData.toList() == from && it.mark == MarkSlot.Concrete(t)
                } && f.ops.leaves(facts).any {
                    it.fact.base == AccessPathBase.Return && it.fact.mark == MarkSlot.Concrete(u)
                }
            }
            if (!hasExitDependency) println(buildString {
                fun image(original: PremiseKey, facts: Facts): String =
                    "${original.members.map { it.toPattern() }} -> ${f.ops.leaves(facts).toList()} layer=${facts.layer}"
                appendLine("NEAREST_STATIC_EXIT_TRACE service=${service.statistics()}")
                for ((original, facts) in actor.summaries.all()) appendLine("ROOT ${image(original, facts)}")
                for ((scope, state) in runtime.states()) {
                    appendLine("SCOPE=$scope initials=${state.initials.all().map { it.toPattern() }}")
                    for ((exit, rows) in state.portSummaries.entries()) for ((original, facts) in rows.all())
                        appendLine("SCOPE=$scope EXIT=$exit ${image(original, facts)}")
                }
                for (row in f.processed)
                    appendLine("AT=${row.node.location.index} ${image(row.premise, row.facts)}")
            })
            assertTrue(hasExitDependency,
                "The actual nearest shortcut must apply the real exit rule before any explicit replay: C.f/T -> ret/U")

            // An equal summary promotion can apply the real exit rule again,
            // but cannot register another physical write point.
            val initial = f.manager.initial(region)
            val result = f.fact(STATIC, to, Tail.STAR, MarkSlot.STAR, layer = Layer.DEMAND)
            actor.routeStaticResultToExit(f.inst(4), initial, result)
            f.drain(actor, quantum = 1)
            assertEquals(writerRows, service.statistics().writerRows,
                "Summary application must not register local writer points")
            actor.freeze()

            fun staticCopy(original: PremiseKey, facts: Facts): Boolean =
                original.members.any { it.base == STATIC && it.pathData.toList() == from } &&
                    facts.layer == Layer.DEMAND && f.ops.leaves(facts).any {
                        it.fact.base == STATIC && it.fact.path == to
                    }
            for (block in listOf(nearest, ancestor)) assertTrue(actor.blockSummaries().any { scoped ->
                scoped.key.scope.block == block && scoped.summaries.all().any { (original, facts) ->
                    staticCopy(original, facts)
                }
            }, "The nearest static copy must reach each internal ancestor through ordinary summaries: $block")
            assertTrue(actor.summaries.all().none { (original, facts) ->
                facts.base == STATIC && !original.isZero && original.members.all { it.base == STATIC }
            }, "Only the public root erases static/static summaries")
        }
    }
}
