package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class LoopBlockStaticExitRulesOnceTest {
    @Test fun `completed ordinary static exit does not replay the real exit source`() {
        // while (again()) { /* no static write */ }
        // EXIT_SOURCE: CM(C.g,T) -> assign U to ret.$.
        // Only the actual ordinary AL invocation may execute this boundary.
        val graph = listOf(listOf(1), listOf(2, 3), listOf(1), listOf(4), emptyList(), emptyList())
        MethodAnalysisFixtures(graph, normalExit = 4, exceptionalExit = 5).use { f ->
            val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
            val cg = listOf(cls, f.field("g"))
            val t = f.mark("T")
            val u = f.mark("U")
            val form = FormKey(FormOwner(), f.key.method, f.key, f.inst(4))
            val occurrence = RuleOccurrenceId(form, RuleKind.EXIT_SOURCE, 0)
            val condition = f.pattern(STATIC, cg, Tail.EXACT, MarkSlot.Concrete(t))
            val target = f.pattern(AccessPathBase.Return, mark = MarkSlot.Concrete(u))
            val builder = RulePredicate.Builder(f.cancellation, f.manager.marks)
            val source = SourceRuleOccurrence(occurrence, builder.build(builder.leaf(condition)),
                listOf(SourceAction(ActionId(occurrence, ActionRole.SOURCE, 0), target.fact)))
            // Match JIRBoundaryForms.exitRules + JIRRuleForms.markInputs: retain
            // the predicate input and install its actual static point interest.
            val statement = MicroEdgeBuilder().apply {
                keepZero()
                keep(STATIC)
                source(source)
                staticOperation(StaticOperation.MarkInput(OperationId(form,
                    action = ActionId(occurrence, ActionRole.MARK_INPUT, 0)), condition))
            }.build()
            f.exitRules(4, ExitRules(RuleStatement(statement, StatementSummary.EMPTY, emptyList()), false, emptySet()))
            var exitAssignments = 0
            f.onCut = { cut, facts ->
                if (cut == Cut.EXIT_RULES && f.ops.leaves(facts).any {
                    it.fact.base == AccessPathBase.Return && it.fact.mark == MarkSlot.Concrete(u)
                }) exitAssignments++
            }
            val actor = f.core(RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key),
                run1MarkMode = MarkMode.FULL), localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            val service = assertNotNull(actor.runnerPort.staticService)
            val region = f.pattern(STATIC, cg, Tail.STAR, MarkSlot.STAR)
            assertTrue(service.commit(StaticBatch().apply {
                writes += region
                supplies += RegionGroups(region, MarkSet.of(t))
            }).isEmpty())
            actor.addRootZero()
            f.drain(actor, quantum = 1)
            assertEquals(1, exitAssignments,
                "The actual source must execute once; final summary deduplication cannot hide a second execution")
            assertTrue(actor.summaries.all().any { (original, result) ->
                original.members.any { it.base == STATIC && it.pathData.toList() == cg && it.mark == MarkSlot.Concrete(t) } &&
                    f.ops.leaves(result).any { it.fact == target.fact }
            }, "The exit source must still produce its genuine C.g/T -> ret/U relation")
            val runtime = assertNotNull(actor.blockRuntime)
            assertTrue(runtime.states().none { (scope, _) -> scope.entry == PortId.ROOT_EXIT },
                "An already completed STATIC result must not create a private raw-write continuation")
            actor.freeze()
            assertTrue(actor.blockSummaries().any { block ->
                block.key.exit == PortId.ROOT_EXIT && block.summaries.all().any { (_, result) ->
                    f.ops.leaves(result).any { it.fact == target.fact }
                }
            })
            assertTrue(actor.blockSummaries().none { it.key.exit == PortId.STATIC_SHORTCUT },
                "This code has no local write and therefore no raw static shortcut")
        }
    }
}
