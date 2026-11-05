package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class LoopCanonicalBoundaryTest {
    @Test fun `newly covered applied MAY child is removed before observer scalarization`() {
        val f=StoreFixtures();val x=AccessPathBase.Argument(0)
        val g=f.field("g");val h=f.field("h")
        val root=f.fact(x,listOf(g),Tail.ANY,MarkSlot.STAR,layer=Layer.DEMAND) as FlowTree
        val child=f.fact(x,listOf(g,h),Tail.ANY,MarkSlot.STAR,layer=Layer.DEMAND) as FlowTree
        val packet=root.withRoot(FlowAlgebra.mergeAdd(root.root,child.root,f.manager.cancellation))
        val keep=AdmittedInitial(f.manager.initial(f.pattern(x,tail=Tail.STAR,mark=MarkSlot.STAR)),Layer.NORMAL)
        val gate=LoopOutputRestriction(f.ops)
        val result=gate.restrict(false,true,packet) { LoopObservation<Unit>(setOf(keep),emptySet(),emptySet()) }
        assertEquals(1L,gate.statistics.scalarQueries,"Canonicalize the complete applied packet before separating its leaves")
        assertEquals(setOf(listOf(g)),result.flatMap{f.ops.leaves(it).map{p->p.fact.path}.toList()}.toSet())
    }

    @Test fun `exclusion-blocked MUST child and protected mask coordinates remain present`() {
        val f=StoreFixtures();val x=AccessPathBase.Argument(0);val field=f.field("f")
        val root=f.fact(x,tail=Tail.ANY_TAINT,mark=MarkSlot.STAR,exclusion=ExclusionSet.of(field)) as FlowTree
        val child=f.fact(x,listOf(field),Tail.ANY_TAINT,MarkSlot.STAR,exclusion=ExclusionSet.of(field)) as FlowTree
        val packet=root.withRoot(FlowAlgebra.mergeAdd(root.root,child.root,f.manager.cancellation))
        val gate=LoopOutputRestriction(f.ops)
        val retained=gate.restrict<Unit>(false,false,packet) { error("A nongrowing row keeps its existing bypass") }.single()
        assertEquals(setOf(emptyList(),listOf(field)),f.ops.leaves(retained).map{it.fact.path}.toSet())
        val t=MarkSlot.Concrete(f.mark("T"));val u=MarkSlot.Concrete(f.mark("U"))
        val parent=f.fact(x,tail=Tail.ANY,mark=t,layer=Layer.DEMAND) as TaintTree
        val protected=f.fact(x,listOf(field),Tail.ANY,t,layer=Layer.DEMAND) as TaintTree
        val other=f.fact(x,listOf(field),Tail.ANY,u,layer=Layer.DEMAND) as TaintTree
        val whole=f.manager.taintAlg.mergeAdd(parent.root,
            f.manager.taintAlg.mergeAdd(protected.root,other.root,f.manager.cancellation),f.manager.cancellation)
        val marked=f.manager.taintTree(x,Layer.DEMAND,whole,ExclusionSet.Empty,Tail.ANY).withProtection(protected.root)
        val kept=gate.restrict<Unit>(false,false,marked) { error("Nongrowing") }.filterIsInstance<TaintTree>().single()
        assertNotNull(kept.nonSubsumable)
        val leaves=f.ops.leaves(kept).toSet()
        assertTrue(f.pattern(x,listOf(field),Tail.ANY,u) in leaves)
        assertTrue(f.pattern(x,listOf(field),Tail.ANY,t) in leaves,"Protected support is not an ordinary redundant child")
    }

    @Test fun `canonical gate keeps separate original offers independent`() {
        val f=StoreFixtures();val x=AccessPathBase.Argument(0);val field=f.field("f")
        val gate=LoopOutputRestriction(f.ops)
        val parent=f.fact(x,tail=Tail.ANY,mark=MarkSlot.STAR,layer=Layer.DEMAND)
        val child=f.fact(x,listOf(field),Tail.ANY,MarkSlot.STAR,layer=Layer.DEMAND)
        assertEquals(listOf(parent),gate.restrict<Unit>(false,false,parent){error("Bypass")})
        assertEquals(listOf(child),gate.restrict<Unit>(false,false,child){error("No history from the prior offer")})
    }

    @Test fun `completion E fill queues every fresh canonical header`() {
        MethodAnalysisFixtures(listOf(listOf(1),listOf(1,2),emptyList(),emptyList()),normalExit=2,exceptionalExit=3).use { f ->
            val actor=f.core(index=5,L=4,demand=DemandStore.Builder(f.manager).build())
            val runtime=assertNotNull(actor.blockRuntime)
            val tree=runtime.layout[runtime.layout.root]
            val child=BlockScope(tree.before!!,PortId.ROOT_ENTRY)
            val exit=runtime.layout.port(0,1)!!.id
            val link=LocalLink(BlockScope.ROOT,exit,f.manager.zero,Layer.NORMAL,child)
            val field=f.field("f");val t=f.mark("T");val u=f.mark("U")
            val first=f.fact(AccessPathBase.Return,listOf(field),Tail.ANY_TAINT,MarkSlot.Concrete(t))
            val incoming=f.manager.taintTree(AccessPathBase.Return,Layer.NORMAL,
                f.manager.taintAlg.leafNode(f.manager.taintLeaves(MarkSet.EMPTY,f.manager.markSetOf(t)+u)),
                ExclusionSet.of(field),Tail.ANY_TAINT)
            // Exercise the actual private boundary adapter without a new production test hook.
            val apply=runtime.javaClass.declaredMethods.single{it.name.startsWith("onApplied")&&it.parameterCount==5}.apply{isAccessible=true}
            val port:Any=if(apply.parameterTypes[1]==Int::class.javaPrimitiveType)exit.ordinal else exit
            val pending=runtime.javaClass.getDeclaredField("pending").apply{isAccessible=true}
            apply.invoke(runtime,link,port,false,f.manager.zero,first)
            val queue=pending.get(runtime) as java.util.ArrayDeque<*>
            assertEquals(1,queue.size)
            apply.invoke(runtime,link,port,false,f.manager.zero,incoming)
            assertEquals(3,queue.size,"Partial T/U fill yields two E headers; both continuations must be queued")
            f.drain(actor,quantum=1)
            runtime.requireIdle()
        }
    }
}
