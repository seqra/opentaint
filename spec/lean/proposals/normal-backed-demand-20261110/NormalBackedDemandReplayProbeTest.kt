package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.EngineShellFixtures
import kotlin.test.*

/** Proposal probe only; source is outside the production/test source tree. */
class NormalBackedDemandReplayProbeTest {
    @Test fun `opposite NORMAL record replays every supported ancestor read lane`() {
        val f=EngineShellFixtures();val ap=f.manager;val ops=ApOps(ap)
        val a=f.field("a");val b=f.field("b");val z=f.field("z")
        val p=AccessPathBase.Argument(0);val q=AccessPathBase.Return
        val mode=ApMode(false,Direction.FORWARD,8)
        fun pattern(base:AccessPathBase,path:List<Int>,tail:Tail,mark:MarkSlot=MarkSlot.STAR)=
            Pattern(PathFact(base,path,tail,mark),ExclusionSet.Empty)
        val read=PathEdge(pattern(p,listOf(a),Tail.STAR).fact,pattern(q,emptyList(),Tail.STAR).fact,ExclusionSet.Empty)
        val view=checkNotNull(reverseRecordLeaf(Direction.BACKWARD,
            pattern(q,emptyList(),Tail.STAR),Conclusion(pattern(p,listOf(a),Tail.STAR).fact,ExclusionSet.Empty,false)))
        assertEquals(read.from,view.premise.fact);assertEquals(read.to,view.result.fact);assertFalse(view.result.demand)
        var checked=0
        for (mark in listOf(MarkSlot.STAR,MarkSlot.Concrete(ap.marks.mark("T"))))
        for (tail in Tail.entries)for (path in listOf(emptyList(),listOf(a),listOf(a,b),listOf(z)))
        for (layer in Layer.entries) {
            if(mark is MarkSlot.Concrete&&tail==Tail.STAR&&layer==Layer.NORMAL)continue
            val value=ap.factsOf(pattern(p,path,tail,mark).fact,ExclusionSet.Empty,layer)
            val origin=ap.initial(pattern(p,emptyList(),Tail.STAR))
            val expected=CollectingOut();ops.applyEdge(value,origin,read,false,mode,expected)
            val actual=CollectingOut();val matched=ops.satisfying(value,view.premise,mode,true,SummaryReadRole.SAVED_OPPOSITE)
            if(matched!=null)ops.applyRecordLeaf(matched,view,false,mode,actual)
            assertEquals(expected.results.toSet(),actual.results.toSet(),"mark=$mark tail=$tail path=$path layer=$layer")
            checked++
        }
        assertEquals(60,checked)
        val broad=ap.factsOf(pattern(p,emptyList(),Tail.STAR).fact,ExclusionSet.Empty,Layer.NORMAL)
        assertNull(ops.satisfying(broad,view.premise,mode,true,SummaryReadRole.SAVED_DIRECT))
        assertNotNull(ops.satisfying(broad,view.premise,mode,true,SummaryReadRole.SAVED_OPPOSITE))
        val out=CollectingOut();ops.applyRecordLeaf(broad,view,false,mode,out)
        assertEquals(listOf(ap.factsOf(pattern(q,emptyList(),Tail.ANY).fact,ExclusionSet.Empty,Layer.DEMAND)),out.results)
    }
}
