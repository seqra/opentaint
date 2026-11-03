package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.MicroEdgeBuilder
import org.opentaint.dataflow.graph.LocalAccess
import java.util.BitSet
import kotlin.test.*

class BlockBoundaryLocalFilterTest {
    private fun access(uses: List<Int> = emptyList(), defs: List<Int> = emptyList()): LocalAccess {
        fun bits(values: List<Int>) = BitSet().apply { values.forEach(::set) }
        return LocalAccess(bits(uses), bits(defs), bits(uses + defs))
    }

    @Test fun `plain copy kills old loop temporary before any boundary summary`() {
        // x is read first on each iteration. tmp is overwritten first.
        MethodAnalysisFixtures(listOf(listOf(1), listOf(2), listOf(3), listOf(1), emptyList()), 4).use { f ->
            val x = AccessPathBase.LocalVar(0); val tmp = AccessPathBase.LocalVar(1)
            f.statement(2, MicroEdgeBuilder().apply { move(tmp, x) }.build())
            f.statement(3, MicroEdgeBuilder().apply { move(AccessPathBase.Return, tmp) }.build())
            f.instructionLocalAccess = listOf(access(), access(), access(listOf(0), listOf(1)), access(listOf(1)), access())
            val actor = f.core(RunConfig(1, 1, null, f.records, org.opentaint.dataflow.bidi.driver.SeedIndex.EMPTY,
                listOf(f.key), run1MarkMode = MarkMode.FULL))
            actor.addInitial(f.manager.initial(f.store.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR)))
            f.drain(actor)
            val rows = actor.joinedBlockStates().flatMap { (_, state) ->
                state.portSummaries.entries().flatMap { it.second.all() }.toList()
            }
            assertTrue(rows.any { it.second.base == x }, "The loop-carried x input must remain")
            assertFalse(rows.any { it.second.base == tmp }, "Old tmp must die before summary/C5/observer work")
            actor.freeze()
        }
    }

    @Test fun `live carried tmp uses native feedback but never leaks onto dead AL route`() {
        MethodAnalysisFixtures(listOf(listOf(1),listOf(2,3),listOf(3),listOf(4),listOf(1,5),listOf(6),emptyList()),6).use { f ->
            val x=AccessPathBase.LocalVar(0); val tmp=AccessPathBase.LocalVar(1)
            f.statement(2,MicroEdgeBuilder().apply { move(tmp,x) }.build())
            f.statement(3,MicroEdgeBuilder().apply { move(AccessPathBase.Return,tmp) }.build())
            f.instructionLocalAccess=listOf(access(),access(),access(listOf(0),listOf(1)),access(listOf(1)),access(),access(),access())
            val actor=f.core(RunConfig(1,1,null,f.records,org.opentaint.dataflow.bidi.driver.SeedIndex.EMPTY,
                listOf(f.key),run1MarkMode=MarkMode.FULL),
                localFactory=MethodLocalServicesFactory(::RunMethodLocalServices))
            actor.addInitial(f.manager.initial(f.store.pattern(x,tail=Tail.STAR,mark=MarkSlot.STAR)))
            f.drain(actor)
            val layout=f.contexts.blockLayout(f.key)
            val loop=layout.blocks.single { it.isLoop }
            val normal=layout.normalExits.single { it.loop==loop.id }
            val rows=actor.joinedBlockStates().filter { it.first.block==loop.id }.flatMap { (_,state) ->
                state.portSummaries.entries().flatMap { (exit,store) -> store.all().map { exit to it.second } }.toList()
            }
            assertTrue(rows.any { it.first in loop.repeatPorts && it.second.base==tmp },"A path reads carried tmp before overwrite")
            assertFalse(rows.any { it.first==normal.id && it.second.base==tmp },"Repeat liveness cannot authorize AL delivery")
            actor.freeze()
        }
    }

    @Test fun `dead local output does not erase NORMAL condition contributor certificates`() {
        MethodAnalysisFixtures(listOf(listOf(1),listOf(2),listOf(3),listOf(1),emptyList()),4).use { f ->
            val x=AccessPathBase.LocalVar(0); val tmp=AccessPathBase.LocalVar(1)
            val t=MarkSlot.Concrete(f.mark("T")); val u=MarkSlot.Concrete(f.mark("U")); val v=MarkSlot.Concrete(f.mark("V"))
            f.statement(2,MicroEdgeBuilder().apply { move(tmp,x) }.build())
            f.statement(3,MicroEdgeBuilder().apply {
                conjunction(ConjunctiveEdge(listOf(f.pattern(tmp,mark=t),f.pattern(tmp,mark=u)),
                    f.pattern(AccessPathBase.Return,mark=v).fact))
            }.build())
            f.instructionLocalAccess=listOf(access(),access(),access(listOf(0),listOf(1)),access(listOf(1)),access())
            val actor=f.core(RunConfig(1,1,null,f.records,org.opentaint.dataflow.bidi.driver.SeedIndex.EMPTY,
                listOf(f.key),run1MarkMode=MarkMode.FULL),
                localFactory=MethodLocalServicesFactory(::RunMethodLocalServices))
            actor.addInitial(f.manager.initial(f.pattern(x,mark=t)))
            actor.addInitial(f.manager.initial(f.pattern(x,mark=u)))
            f.drain(actor)
            assertFalse(actor.joinedBlockStates().any { (_,state) ->
                state.portSummaries.entries().any { (_,store) -> store.all().any { it.second.base==tmp } }
            })
            actor.freeze()
            assertTrue(actor.normalContributorRows().any { it.input.facts?.base==tmp },
                "The completed condition observation must survive boundary erasure")
        }
    }
}
