package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.Cut
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

class LoopBlockCyclicEntryTest {
    @Test fun `a cyclic first instruction repeats its transfer without repeating method entry rules`() {
        // The method starts with a real field read, not an identity sentinel:
        // entry rules source x.f.f; do { x=x.f; } while(again()); exit.
        MethodAnalysisFixtures(listOf(listOf(1), listOf(0, 2), emptyList(), emptyList()),
            normalExit = 2, exceptionalExit = 3).use { f ->
            val x = AccessPathBase.Argument(0)
            val field = f.field("f")
            val source = PathEdge(ZERO_FACT,
                f.pattern(x, listOf(field, field)).fact, ExclusionSet.Empty)
            f.entryRules(RuleStatement(StatementSummary(setOf(AccessPathBase.Zero),
                listOf(MicroEdge.of(ZERO_KEEP), MicroEdge.of(source)), emptyList(), emptyMap()),
                StatementSummary.EMPTY, emptyList()))
            f.statement(0, MicroEdgeBuilder().apply { read(x, x, listOf(field)) }.build())
            var entrySourceCuts = 0
            f.onCut = { cut, facts ->
                if (cut == Cut.ENTRY_RULES && facts.base == x && facts is TaintTree) entrySourceCuts++
            }
            val actor = f.core()
            actor.addRootZero()
            f.drain(actor, quantum = 1)
            assertEquals(1, entrySourceCuts, "Method entry rules are not copied into a repeated block")
            val runtime = assertNotNull(actor.blockRuntime)
            val loop = runtime.layout.ownerOf(0)
            assertTrue(runtime.layout[loop].isLoop)
            assertTrue(f.processed.any { it.node.location.index == 0 && it.facts is FlowTree },
                "The original first-instruction transfer executes again in its loop scope")
            assertTrue(runtime.states().filter { it.first.block == loop }.any { (_, state) ->
                state.edges.edgesAt(f.inst(0)).any { (_, facts) ->
                    facts is FlowTree && facts.base == x && facts.tail == Tail.ANY
                }
            }, "The repeated x=x.f read must produce its ordinary incomplete FLOW result")
            val before = assertNotNull(runtime.layout[runtime.layout.root].before)
            val repeatPorts = runtime.layout[loop].repeatPorts.toSet()
            assertTrue(runtime.states().none { (scope, _) -> scope.block == before && scope.entry in repeatPorts },
                "Loop repeat enters L directly, without replaying BL admission")
        }
    }
}
