package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import org.opentaint.ir.api.common.cfg.CommonInst
import kotlin.test.*

class PreparedSummaryFallbackTest {
    private fun checkBoundary(token: PreparedExit?, keep: () -> Boolean, expectedRows: Int) {
        MethodAnalysisFixtures(listOf(listOf(1),emptyList()),1).use { f ->
            val scope = BlockScope(BlockId(7),PortId(2))
            val exit = PortId(3)
            val x = AccessPathBase.Argument(0)
            val local = AccessPathBase.LocalVar(1)
            val t = MarkSlot.Concrete(f.mark("T"))
            val original = f.manager.initial(f.pattern(x,mark=t))
            val value = f.fact(local,mark=t)
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key,scope,exit,DemandPattern(f.pattern(x,mark=t),f.pattern(local,mark=t)))
            }.build()
            val root = f.core(index=3,L=2,demand=demand)
            val binding = SummaryBinding(scope,root.context,demand.scope(f.key,scope),token,keep)
            val state = BlockRunState(f.key,root.runnerPort,PublicationSink { _, _ -> },
                MethodLocalServicesFactory(::RunMethodLocalServices),
                MethodCallServicesFactory(::RunMethodCallServices),TargetPublicationSink { _, _ -> },binding)
            state.retainBlockSummary(exit,original,value)
            while (!state.workLocal(16)) { }
            try {
                val rows = state.portSummaries.entries().flatMap { it.second.all() }.toList()
                assertEquals(expectedRows,rows.size)
                if (expectedRows != 0) {
                    assertEquals(original,rows.single().first)
                    assertEquals(value,rows.single().second)
                }
            } finally {
                state.freeze()
                root.freeze()
            }
        }
    }

    @Test fun `unknown prepared adapter retains custom native dead local filtering`() {
        var checks=0
        checkBoundary(null,{ checks++; false },expectedRows=0)
        assertEquals(1,checks)
    }

    @Test fun `unknown prepared adapter keeps live data using its native guard`() {
        var checks=0
        checkBoundary(null,{ checks++; true },expectedRows=1)
        assertEquals(1,checks)
    }

    @Test fun `prepared live routes do not repeat the native local predicate`() {
        checkBoundary(PreparedExit.Terminal(PortId(3)),{ error("A prepared route already checked liveness") },expectedRows=1)
    }

    @Test fun `prepared dead routes never invoke native C5 or its local predicate`() {
        checkBoundary(PreparedExit.DeadData,{ error("A prepared dead route is final") },expectedRows=0)
    }

    private class SummaryBinding(
        override val scope: BlockScope,
        override val context: RunMethodContext,
        override val demand: ScopeDemandView,
        private val token: PreparedExit?,
        private val keep: () -> Boolean,
    ) : BlockRuntimeBinding {
        override val points = object : PointDirectory<CommonInst> {
            override val size=0
            override fun index(point: CommonInst): Int = error("No physical statement in this boundary control")
        }
        override val bodyWork: BodyWorkStatistics? = null
        override val sourceHits: SourceHitStore? = null
        override val sinkSeeds = LinkedHashSet<org.opentaint.dataflow.bidi.driver.Seed>()
        override fun keepLocalConclusion(exit: PortId,value: Facts)=keep()
        override fun prepareExit(exit: PortId,base: AccessPathBase)=token
        override fun schedule()=Unit
        override fun publish(state: BlockRunState,exit: PortId,publications: List<Publication>)=Unit
        override fun start(state: BlockRunState,original: InitialAp,value: Facts)=error("unused")
        override fun startResult(state: BlockRunState,node: CommonInst,original: PremiseKey,value: Facts)=error("unused")
        override fun successors(state: BlockRunState,node: CommonInst,original: PremiseKey,value: Facts)=error("unused")
        override fun publishTargets(state: BlockRunState,targets: TargetBatch)=error("unused")
        override fun borrowRequests(input: Facts): List<RequestedRow> = emptyList()
        override fun borrowRequest(slot: Run1Slot): RequestRowView=error("unused")
        override fun commitRequests(state: BlockRunState,temporary: RequestStorage)=error("unused")
        override fun staticMarkRequest(initial: InitialAp,mark: TaintMark)=error("unused")
        override fun staticTicket(): Long=error("unused")
        override fun routeStaticToExit(state: BlockRunState,node: CommonInst,original: PremiseKey,value: Facts)=error("unused")
        override fun methodBoundary(state: BlockRunState,node: CommonInst,original: PremiseKey,value: Facts,summary: Boolean)=error("unused")
    }
}
