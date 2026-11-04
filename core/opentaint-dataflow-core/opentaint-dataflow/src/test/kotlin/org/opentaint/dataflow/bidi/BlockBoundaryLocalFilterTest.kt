package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.MicroEdgeBuilder
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.PortId
import org.opentaint.dataflow.graph.LocalAccess
import java.util.BitSet
import kotlin.test.*

class BlockBoundaryLocalFilterTest {
    private fun access(uses: List<Int> = emptyList(), defs: List<Int> = emptyList()): LocalAccess {
        fun bits(values: List<Int>) = BitSet().apply { values.forEach(::set) }
        return LocalAccess(bits(uses), bits(defs), bits(uses + defs))
    }

    @Test fun `dead DATA from a native saved application still delivers its excluded mark request`() {
        // while (again()) {} ; exit. The saved body relation has a dead local image.
        // Applying its excluded FLOW target must still request T at the real parent input.
        MethodAnalysisFixtures(listOf(listOf(1),listOf(2,4),listOf(3),listOf(1),listOf(5),emptyList()),5).use { f ->
            val x=AccessPathBase.Argument(0)
            val dead=AccessPathBase.LocalVar(7)
            val t=f.mark("T")
            f.instructionLocalAccess=List(6) { access() }
            val layout=f.contexts.blockLayout(f.key)
            val loop=layout.blocks.single { it.isLoop }
            val input=layout.port(0,1)!!.id
            val output=layout.normalExits.single { it.loop==loop.id }.id
            val initial=f.manager.initial(f.pattern(x,tail=Tail.STAR,mark=MarkSlot.STAR))
            val result=f.fact(dead,tail=Tail.STAR,mark=MarkSlot.Star(f.manager.markSetOf(t)))
            f.records.add(Record(f.key,Direction.FORWARD,initial,result,BlockScope(loop.id,input),output))
            val actor=f.core(RunConfig(1,1,null,f.records,org.opentaint.dataflow.bidi.driver.SeedIndex.EMPTY,
                listOf(f.key),run1MarkMode=MarkMode.FULL),
                localFactory=MethodLocalServicesFactory(::RunMethodLocalServices))
            actor.addInitial(initial)
            f.drain(actor,quantum=1)
            assertTrue(t in f.requestRow(actor,assertNotNull(Run1Slot.fromInitial(initial))),
                "Native saved application must execute the generic exclusion creator before DATA is discarded")
            assertFalse(actor.joinedBlockStates().any { (_,state) ->
                state.portSummaries.entries().any { (_,store) -> store.all().any { it.second.base==dead } }
            },"No dead local may enter admitted DATA storage")
            assertFalse(actor.summaries.all().any { it.second.base==dead })
            actor.freeze()
        }
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
