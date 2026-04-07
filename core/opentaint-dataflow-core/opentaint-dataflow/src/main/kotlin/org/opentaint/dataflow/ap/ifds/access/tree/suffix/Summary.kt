package org.opentaint.dataflow.ap.ifds.access.tree.suffix

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary.FactSEBuilder
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary.SideEffectExclusionMergingStorage
import org.opentaint.dataflow.ap.ifds.access.common.CommonNDF2FSummary
import org.opentaint.dataflow.ap.ifds.access.common.CommonSeReqStorage
import org.opentaint.dataflow.ap.ifds.access.common.CommonZ2FSummary
import org.opentaint.ir.api.common.cfg.CommonInst

class FinalSummaries(
    methodInitialStatement: CommonInst,
    override val apManager: TreeSuffixApManager,
) : CommonZ2FSummary<FactAccess>(methodInitialStatement), TreeSuffixFinalFactAccess {
    override fun createStorage(): Storage<FactAccess> = FinalSummaryStorage()

    private class FinalSummaryStorage : Storage<FactAccess> {
        override fun add(edges: List<FactAccess>, added: MutableList<Z2FBBuilder<FactAccess>>) {
            TODO("Not yet implemented")
        }

        override fun collectEdges(dst: MutableList<Z2FBBuilder<FactAccess>>) {
            TODO("Not yet implemented")
        }
    }
}

class F2FSummaries(
    methodInitialStatement: CommonInst,
    override val apManager: TreeSuffixApManager,
) : CommonF2FSummary<FactAccess, FactAccess>(methodInitialStatement),
    TreeSuffixInitialFactAccess,
    TreeSuffixFinalFactAccess {

    override fun createStorage(): Storage<FactAccess, FactAccess> = F2FSummaryStorage()

    private class F2FSummaryStorage : Storage<FactAccess, FactAccess> {
        override fun add(
            edges: List<StorageEdge<FactAccess, FactAccess>>,
            added: MutableList<F2FBBuilder<FactAccess, FactAccess>>
        ) {
            TODO("Not yet implemented")
        }

        override fun collectSummariesTo(
            dst: MutableList<F2FBBuilder<FactAccess, FactAccess>>,
            initialFactPatter: FactAccess?
        ) {
            TODO("Not yet implemented")
        }
    }

    private class F2FSummaryBuilder : F2FBBuilder<FactAccess, FactAccess>(),
        TreeSuffixInitialFactAccess,
        TreeSuffixFinalFactAccess {
        override val apManager: TreeSuffixApManager
            get() = TODO("Not yet implemented")

        override fun nonNullIAP(iap: FactAccess?): FactAccess {
            TODO("Not yet implemented")
        }
    }
}

class NdF2FSummaries(
    methodInitialStatement: CommonInst,
    override val apManager: TreeSuffixApManager,
) : CommonNDF2FSummary<FactAccess>(methodInitialStatement), TreeSuffixFinalFactAccess {
    override fun createStorage(): Storage<FactAccess> = NdF2FSummaryStorage()

    private class NdF2FSummaryStorage : Storage<FactAccess> {
        override fun add(edges: List<SimpleNdEdge<FactAccess>>, added: MutableList<NDF2FBBuilder<FactAccess>>) {
            TODO("Not yet implemented")
        }

        override fun filterTo(
            dst: MutableList<NDF2FBBuilder<FactAccess>>,
            initialFactPattern: org.opentaint.dataflow.ap.ifds.access.FinalFactAp?
        ) {
            TODO("Not yet implemented")
        }
    }

    private class NdF2FSummaryBuilder : NDF2FBBuilder<FactAccess>(), TreeSuffixFinalFactAccess {
        override val apManager: TreeSuffixApManager
            get() = TODO("Not yet implemented")
    }
}

class SeReqSummaries(
    override val apManager: TreeSuffixApManager,
) : CommonSeReqStorage<FactAccess, FactAccess>(),
    TreeSuffixInitialFactAccess,
    TreeSuffixFinalFactAccess {
    override fun createStorage(): Storage<FactAccess, FactAccess> = ReqStorage()

    class ReqStorage : Storage<FactAccess, FactAccess> {
        override fun add(
            requirement: FactAccess,
            exclusionSet: ExclusionSet
        ): Boolean {
            TODO("Not yet implemented")
        }

        override fun getAndResetDelta(delta: MutableList<Pair<FactAccess, ExclusionSet>>) {
            TODO("Not yet implemented")
        }

        override fun find(
            dst: MutableList<Pair<FactAccess, ExclusionSet>>,
            pattern: FactAccess?
        ) {
            TODO("Not yet implemented")
        }
    }
}

class SeFactSummaries(
    methodInitialStatement: CommonInst,
    override val apManager: TreeSuffixApManager,
) : CommonFactSideEffectSummary<FactAccess, FactAccess>(methodInitialStatement),
    TreeSuffixInitialFactAccess,
    TreeSuffixFinalFactAccess {
    override fun createStorage(): Storage<FactAccess, FactAccess> =
        TaintedSESummariesGroupedByFactStorage(apManager)
}

private class TaintedSESummariesInitialApStorage(
    val apManager: TreeSuffixApManager,
) {
    fun getOrCreate(initialAccess: FactAccess): TaintedSESummariesMergingStorage {
        TODO("Not yet implemented")
    }

    fun filterSummariesTo(
        dst: MutableList<FactSEBuilder<FactAccess>>,
        containsPattern: FactAccess,
    ) {
        TODO("Not yet implemented")
    }

    fun collectAllSummariesTo(dst: MutableList<FactSEBuilder<FactAccess>>) {
        TODO("Not yet implemented")
    }
}

private class TaintedSESummariesGroupedByFactStorage(
    private val apManager: TreeSuffixApManager,
) : CommonFactSideEffectSummary.Storage<FactAccess, FactAccess> {
    private val storageRoot = TaintedSESummariesInitialApStorage(apManager)

    override fun add(
        iap: FactAccess,
        se: Map<SideEffectKind, ExclusionSet>,
        added: MutableList<FactSEBuilder<FactAccess>>,
    ) {
        TODO("Not yet implemented")
    }

    override fun collectSummariesTo(
        dst: MutableList<FactSEBuilder<FactAccess>>,
        initialFactPattern: FactAccess?,
    ) {
        TODO("Not yet implemented")
    }
}

private class TaintedSESummariesMergingStorage(
    val apManager: TreeSuffixApManager,
    val initialAccess: FactAccess,
) : SideEffectExclusionMergingStorage<FactAccess>() {
    override fun createBuilder(): FactSEBuilder<FactAccess> {
        TODO("Not yet implemented")
    }
}

private class FactSETreeSuffixApBuilder(
    override val apManager: TreeSuffixApManager,
) : FactSEBuilder<FactAccess>(),
    TreeSuffixInitialFactAccess,
    TreeSuffixFinalFactAccess {
    override fun nonNullIAP(iap: FactAccess?): FactAccess {
        TODO("Not yet implemented")
    }
}
