package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.SummaryEdgeSubscriptionManager.FactEdgeSummarySubscription
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import kotlin.test.Test
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class BaseOnlySubscriptionAndReqTest {
    private val manager = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled)
    private val mark = TaintMarkAccessor("m")

    private val inst = object : CommonInst {
        override fun toString(): String = "i0"
        override val location: CommonInstLocation get() = error("unused")
    }

    @Test
    fun `subscription dedups fact to fact registration`() {
        val sub = manager.accessPathSubscription()
        val callerInitial = manager.mostAbstractInitialAp(AccessPathBase.This).prependAccessor(mark)
        val callerExit = manager.createFinalAp(AccessPathBase.Return, ExclusionSet.Universe).prependAccessor(mark)

        assertNotNull(sub.addFactToFact(inst, AccessPathBase.This, callerInitial, callerExit))
        assertNull(sub.addFactToFact(inst, AccessPathBase.This, callerInitial, callerExit))

        val collected = mutableListOf<FactEdgeSummarySubscription>()
        val summaryInitial = manager.mostAbstractInitialAp(AccessPathBase.This).prependAccessor(mark)
        sub.collectFactEdge(collected, summaryInitial, emptyDeltaRequired = false)
        assertTrue(collected.isNotEmpty(), "registered subscription is collected")
    }

    @Test
    fun `side effect requirement dedups and filters by base`() {
        val storage = manager.sideEffectRequirementApStorage()
        val requirement = manager.mostAbstractInitialAp(AccessPathBase.This).prependAccessor(mark)

        assertTrue(storage.add(listOf(requirement)).isNotEmpty(), "first requirement is new")
        assertTrue(storage.add(listOf(requirement)).isEmpty(), "same requirement subsumed")

        val matching = mutableListOf<InitialFactAp>()
        storage.filterTo(matching, manager.createFinalAp(AccessPathBase.This, ExclusionSet.Universe))
        assertTrue(matching.isNotEmpty(), "requirement filtered by matching base")

        val other = mutableListOf<InitialFactAp>()
        storage.filterTo(other, manager.createFinalAp(AccessPathBase.Return, ExclusionSet.Universe))
        assertTrue(other.isEmpty(), "no requirement for unrelated base")

        val all = mutableListOf<InitialFactAp>()
        storage.collectAllRequirementsTo(all)
        assertTrue(all.isNotEmpty())
    }
}
