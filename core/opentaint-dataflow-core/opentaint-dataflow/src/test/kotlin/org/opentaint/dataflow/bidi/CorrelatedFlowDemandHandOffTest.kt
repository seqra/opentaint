package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.HandOff
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.driver.projectBlockHandOff
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

/** Regression for Conductor's run-3 barrier: C5 can retain correlated STAR/FLOW on DEMAND.
 * These are explicit C5 component inputs, not a claim to replay the actual project row. */
class CorrelatedFlowDemandHandOffTest {
    private fun pattern(base: AccessPathBase, path: List<Int> = emptyList(), tail: Tail = Tail.STAR,
                        mark: MarkSlot = MarkSlot.STAR, exclusion: ExclusionSet = ExclusionSet.Empty) =
        Pattern(PathFact(base,path,tail,mark),exclusion)

    @Test fun `paired C5 STAR demand reaches the next method run without losing correlation`() {
        for(run in listOf(3,4)) for(withExclusion in listOf(false,true)) MethodAnalysisFixtures().use { f ->
            val p=if(run%2==1) AccessPathBase.Argument(0) else AccessPathBase.Return
            val c=if(run%2==1) AccessPathBase.Return else AccessPathBase.Argument(0)
            val field=f.field("requested")
            val other=f.field("excluded")
            val t=MarkSlot.Concrete(f.mark("T"))
            val u=f.mark("U")
            val dc=pattern(p,tail=Tail.ANY,mark=t)
            val dp=pattern(c,listOf(field),Tail.ANY,t)
            val incoming=DemandStore.Builder(f.manager).apply { add(f.key,DemandPattern(dc,dp)) }.build()
            val config=RunConfig(run,run-1,incoming,f.records,SeedIndex.EMPTY,listOf(f.key),run1MarkMode=MarkMode.FULL)
            val actor=f.core(config)
            val initial=f.manager.initial(pattern(p))
            val e=if(withExclusion) ExclusionSet.of(other) else ExclusionSet.Empty
            val raw=f.fact(c,tail=Tail.STAR,mark=MarkSlot.Star(f.manager.markSetOf(u)),
                exclusion=e,layer=Layer.DEMAND)
            // Concrete dc authorizes the STAR/FLOW companion. C5 keeps an ancestor
            // STAR conclusion whole; no field suffix exceeds this pair's FL+1 cap.
            actor.summaryDelta(initial,raw)
            f.drain(actor)
            val retained=actor.summaries.all().toList()
            assertEquals(listOf(initial to raw),retained)
            assertEquals(Tail.STAR,(retained.single().second as FlowTree).tail)
            actor.freeze()
            val result=RunResult(RunStatus.COMPLETE,listOf(actor),run,config.direction)
            val handoff=HandOff.of(config,result,f.shared)
            val expected=DemandPattern(pattern(c),pattern(p))
            assertEquals(listOf(expected),handoff.demand.explicitRows(f.key))
            assertEquals(mapOf(f.key to 1),handoff.demandEdges)
            assertEquals(retained,actor.summaries.all().toList(),"Projection must not rewrite raw E/mx/layer")
            val next=RunConfig(run+1,run,handoff.demand,f.records,handoff.seeds,listOf(f.key),run1MarkMode=MarkMode.FULL)
            val sameHead=f.fact(c,tail=Tail.STAR,mark=t,layer=Layer.DEMAND)
            val starts=handoff.demand.initials(f.key,sameHead,next.admissionPolicy)
            assertEquals(setOf(AdmittedInitial(f.manager.initial(pattern(c,tail=Tail.EXACT)),Layer.NORMAL)),starts)
            assertTrue(handoff.demand.initials(f.key,f.fact(c,listOf(field),Tail.EXACT,t),next.admissionPolicy).isEmpty(),
                "Accepting stored STAR guidance does not permit later STAR-demand refinement")
        }
    }

    @Test fun `C5 exact FLOW selection normalizes a raw MAY demand before method handoff`() {
        MethodAnalysisFixtures().use { f ->
            val p=AccessPathBase.Argument(0)
            val ret=AccessPathBase.Return
            val t=MarkSlot.Concrete(f.mark("T"))
            val u=f.mark("U")
            val pair=DemandPattern(pattern(p,tail=Tail.ANY,mark=t),pattern(ret,tail=Tail.EXACT,mark=t))
            val incoming=DemandStore.Builder(f.manager).apply { add(f.key,pair) }.build()
            val config=RunConfig(3,2,incoming,f.records,SeedIndex.EMPTY,listOf(f.key),run1MarkMode=MarkMode.FULL)
            val initial=f.manager.initial(pattern(p))
            val raw=f.fact(ret,tail=Tail.ANY,mark=MarkSlot.Star(f.manager.markSetOf(u)),layer=Layer.DEMAND)
            // The old pre-C5 ANY guard accepts raw. Exact output demand first
            // selects EXACT/FLOW on DEMAND; public FLOW normalization then yields
            // STAR/FLOW on DEMAND. The old post-C5 ANY guard rejected that result.
            val rawLeaf=f.ops.leaves(raw).single()
            val selected=assertNotNull(restrict(initial.toPattern(),
                Conclusion(rawLeaf.fact,rawLeaf.exclusion,true),pair,f.manager.marks,config.admissionPolicy))
            assertEquals(Tail.EXACT,selected.fact.tail)
            assertTrue(selected.demand)
            val actor=f.core(config)
            actor.summaryDelta(initial,raw)
            f.drain(actor)
            val public=actor.summaries.all().single().second as FlowTree
            assertEquals(Tail.STAR,public.tail)
            assertEquals(Layer.DEMAND,public.layer)
            assertEquals(ExclusionSet.Empty,public.exclusion)
            assertEquals((raw as FlowTree).markExclusion,public.markExclusion)
            assertEquals(raw.root,public.root)
            actor.freeze()
            val handoff=HandOff.of(config,RunResult(RunStatus.COMPLETE,listOf(actor),3,Direction.FORWARD),f.shared)
            assertEquals(listOf(DemandPattern(pattern(ret),pattern(p))),handoff.demand.explicitRows(f.key))
            assertEquals(mapOf(f.key to 1),handoff.demandEdges)
            val next=RunConfig(4,3,handoff.demand,f.records,handoff.seeds,listOf(f.key))
            assertEquals(setOf(AdmittedInitial(f.manager.initial(pattern(ret,tail=Tail.EXACT)),Layer.NORMAL)),
                handoff.demand.initials(f.key,f.fact(ret,tail=Tail.EXACT,mark=t),next.admissionPolicy))
        }
    }

    @Test fun `block C5 STAR demand reverses its exact ports and validates in the next run`() {
        val fixture=StoreFixtures()
        val ap=fixture.manager
        val method=fixture.method
        val p=AccessPathBase.LocalVar(1)
        val c=AccessPathBase.LocalVar(2)
        val field=fixture.field("requested")
        val excluded=fixture.field("excluded")
        val t=MarkSlot.Concrete(fixture.mark("T"))
        val scope=BlockScope(BlockId(2),PortId(7))
        val exit=PortId(8)
        val owner=ScopedSummaryKey(method,scope,exit)
        for(run in listOf(3,4)) {
            val direction=if(run%2==1) Direction.FORWARD else Direction.BACKWARD
            val policy=RestrictedInitialPolicy(run,run-1,direction,ap.marks)
            val previous=DemandStore.Builder(ap).apply {
                add(method,scope,exit,DemandPattern(pattern(p,tail=Tail.ANY,mark=t),
                    pattern(c,listOf(field),Tail.ANY,t)))
            }.build()
            val initial=ap.initial(pattern(p))
            val raw=ap.factsOf(pattern(c,exclusion=ExclusionSet.of(excluded)).fact,
                ExclusionSet.of(excluded),Layer.DEMAND)
            val admitted=previous.scope(method,scope).intersect(exit,initial,raw,policy)
            assertEquals(listOf(raw),admitted)
            val store=RunSummaryStore(ap).apply { admitted.forEach { addAdmitted(initial,it) } }
            val builder=DemandStore.Builder(ap)
            val counts=LinkedHashMap<MethodKey,Int>()
            val projected=ArrayList<Pair<Pattern,Pattern>>()
            projectBlockHandOff(ap,direction,false,sequenceOf(ScopedRunSummary(owner,store)),
                emptySequence(),builder,counts) { key,from,to ->
                assertEquals(owner,key)
                projected += from to to
            }
            val outgoing=builder.build()
            assertEquals(listOf(pattern(p) to pattern(c)),projected)
            assertEquals(mapOf(method to 1),counts)
            val next=RunConfig(run+1,run,outgoing,PersistentRecordStore(ap),SeedIndex.EMPTY,listOf(method))
            val query=outgoing.scope(method,owner.reversed().scope)
            val actual=ap.factsOf(pattern(c,tail=Tail.EXACT,mark=t).fact,ExclusionSet.Empty,Layer.NORMAL)
            val start=query.initials(actual,next.admissionPolicy).single()
            assertEquals(pattern(c,tail=Tail.EXACT),start.initial.toPattern())
            val answer=ap.factsOf(pattern(p).fact,ExclusionSet.Empty,Layer.DEMAND)
            assertEquals(listOf(answer),query.intersect(scope.entry,start.initial,answer,next.admissionPolicy))
            assertTrue(query.intersect(exit,start.initial,answer,next.admissionPolicy).isEmpty())
            assertTrue(outgoing.initials(method,actual,next.admissionPolicy).isEmpty(),
                "Internal local guidance must not leak into the public method interface")
        }
    }
}
