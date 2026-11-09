package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class LoopQueryScratchTest {
    private val f = StoreFixtures()
    private val x = AccessPathBase.Argument(0)
    private val t = MarkSlot.Concrete(f.mark("T"))
    private val policy = RestrictedInitialPolicy(3,4,Direction.FORWARD,f.manager.marks)
    private fun view(query: (Facts) -> Set<AdmittedInitial>) = object : ScopeDemandView {
        override fun initials(actual: Facts, policy: RestrictedInitialPolicy) = query(actual)
        override fun intersect(exit: PortId, original: PremiseKey, raw: Facts, policy: RestrictedInitialPolicy) = emptyList<Facts>()
        override fun acceptsTarget(exit: PortId, original: PremiseKey, policy: RestrictedInitialPolicy) = false
    }

    @Test fun `empty hits and full protection masks remain distinct and scratch clears`() {
        var calls = 0
        val view = view { calls++; emptySet() }
        val counts = LoopQueryCounts(); val scratch = LoopQueryScratch(f.manager, counts)
        val a = f.fact(x, listOf(f.field("a")), mark = t) as TaintTree
        val b = f.fact(x, listOf(f.field("b")), mark = t) as TaintTree
        val both = f.manager.mergeAddDelta(a,b).first as TaintTree
        val protectedA = both.withProtection(a.root)
        val protectedB = both.withProtection(b.root)
        assertNotEquals(protectedA, protectedB)
        scratch.initials(view,protectedA,policy)
        scratch.initials(view,protectedA,policy)
        scratch.initials(view,protectedB,policy)
        assertEquals(2,calls); assertEquals(1,counts.c2Hits)
        scratch.clear(); assertEquals(0,scratch.retainedAdmissionCount)
        scratch.initials(view,protectedA,policy); assertEquals(3,calls)
    }

    @Test fun `one observation uses each oversize answer once and preserves phase order`() {
        val order = ArrayList<String>()
        val scope = BlockScope(BlockId(1),PortId(2))
        val answers = (0..128).map { AdmittedInitial(f.manager.initial(f.pattern(x,
            listOf(f.field("f$it")), mark=t)),Layer.NORMAL) }
        val bundle = LoopAdmissionBundle(
            { order += "adjacent"; answers.map { LoopLabelledAdmission(scope,LoopAdmissionFamily.ADJACENT,it) } },
            { order += "repeat"; answers.map { LoopLabelledAdmission(scope,LoopAdmissionFamily.REPEAT,it) } })
        assertEquals(129,bundle.adjacent().size)
        order += "enclosing"
        assertEquals(129,bundle.repeat().size)
        assertEquals(258,bundle.labelled().size)
        assertEquals(listOf("adjacent","enclosing","repeat"),order)
    }

    @Test fun `capacity and oversize answers cannot change admission`() {
        val scratch = LoopQueryScratch(f.manager,LoopQueryCounts())
        val expected = (0..128).mapTo(LinkedHashSet()) { AdmittedInitial(f.manager.initial(f.pattern(x,
            listOf(f.field("v$it")),mark=t)),Layer.NORMAL) }
        var calls = 0
        val large = view { calls++; expected }
        repeat(2) { assertEquals(expected,scratch.initials(large,f.fact(x,mark=t),policy)) }
        assertEquals(2,calls); assertEquals(0,scratch.retainedAdmissionCount)
        val small = view { emptySet() }
        repeat(40) { scratch.initials(small,f.fact(x,listOf(f.field("k$it")),mark=t),policy) }
        assertTrue(scratch.retainedAdmissionCount <= 32)
    }

    @Test fun `oversize ND original never becomes a retained positive or negative key`() {
        val members = (0..2048).map { f.manager.initial(f.pattern(x,listOf(f.field("m$it")),mark=t)) }
        val original = f.manager.premiseOf(members)
        val templates = members.map { it.toPattern() }
        val scratch = LoopQueryScratch(f.manager,LoopQueryCounts())
        var called = false
        assertNull(scratch.plan(Any(),PortId(3),original,templates,policy) { called=true; null })
        assertFalse(called)
        assertEquals(0,scratch.retainedPlanCount)
        assertNull(DemandStore.Builder(f.manager).build().prepareDataPlan(f.method,templates,policy))
    }

    @Test fun `plan memo keeps raw whole origins and exact exits separate`() {
        val scratch = LoopQueryScratch(f.manager,LoopQueryCounts())
        val exact = f.manager.initial(f.pattern(x,tail=Tail.EXACT,mark=MarkSlot.STAR))
        val broad = f.manager.initial(f.pattern(x,tail=Tail.STAR,mark=MarkSlot.STAR))
        val templates = listOf(broad.toPattern())
        val view = Any()
        var prepared=0
        fun offer(original: PremiseKey, exit: PortId) = scratch.plan(view,exit,original,templates,policy) { prepared++; null }
        offer(exact,PortId(1)); offer(exact,PortId(1))
        offer(broad,PortId(1)); offer(exact,PortId(2))
        assertEquals(3,prepared)
        assertEquals(3,scratch.retainedPlanCount)
    }
}
