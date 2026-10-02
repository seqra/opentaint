package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.CommonNDF2FSummary
import org.opentaint.dataflow.ap.ifds.access.common.ndf2f.DefaultNDF2FSummaryStorage
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode
import org.opentaint.dataflow.util.PersistentBitSet.Companion.emptyPersistentBitSet
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.BitSet

class MethodNDInitialToFinalApSummaries(
    private val methodInitialStatement: CommonInst,
    override val apManager: TreeApManager,
) : CommonNDF2FSummary<AccessNode>(methodInitialStatement),
    TreeFinalApAccess {
    private class NDFactToFactEdgeBuilderBuilder(
        override val apManager: TreeApManager,
    ) : NDF2FBBuilder<AccessNode>(), TreeFinalApAccess

    override fun createStorage(): Storage<AccessNode> = object :
        DefaultNDF2FSummaryStorage<AccessPath.AccessNode?, AccessNode>() {
        private val initialApIndex = AccessPathInterner(apManager, methodInitialStatement)
        private val initialAp = arrayListOf<AccessPath>()

        override fun initialApIdx(ap: InitialFactAp): Int {
            ap as AccessPath
            return initialApIndex.getOrCreateIndex(ap.base, ap.access) {
                initialAp.add(ap)
            }
        }

        override fun getInitialApByIdx(idx: Int): InitialFactAp = initialAp[idx]

        override fun createBuilder(): NDF2FBBuilder<AccessNode> =
            NDFactToFactEdgeBuilderBuilder(apManager)

        override fun relevantInitialAp(summaryInitialFactPattern: FinalFactAp): BitSet =
            initialApIndex.findBaseIndices(summaryInitialFactPattern.base) ?: emptyPersistentBitSet()

        override fun createStorage(idx: Int): Storage<AccessPath.AccessNode?, AccessNode> =
            FactStorage(idx)

        private inner class FactStorage(
            override val storageIdx: Int,
        ) : Storage<AccessPath.AccessNode?, AccessNode> {
            // an index whose initial set has an AP with [any] keeps everything in the any part
            private val anyInitial: Boolean = initialApStorage[storageIdx].stream().anyMatch { apIdx ->
                (getInitialApByIdx(apIdx) as AccessPath).access?.containsAny == true
            }

            private val complete = FinalTrees()
            private val any = FinalTrees()

            override fun add(element: AccessNode): Storage<AccessPath.AccessNode?, AccessNode>? {
                if (anyInitial) return if (any.add(element)) this else null
                if (!element.containsAny) return if (complete.add(element)) this else null

                val split = element.splitAny()
                val completeModified = split.complete?.let { complete.add(it) } ?: false
                val anyModified = split.any?.let { any.add(it) } ?: false
                return if (completeModified || anyModified) this else null
            }

            override fun getAndResetDelta(delta: MutableList<AccessNode>) {
                complete.getAndResetDelta(delta)
                any.getAndResetDelta(delta)
            }

            override fun collectTo(dst: MutableList<AccessNode>) {
                collectCompleteTo(dst)
                collectAnyTo(dst)
            }

            fun collectCompleteTo(dst: MutableList<AccessNode>) {
                complete.edges?.let { dst += it }
            }

            fun collectAnyTo(dst: MutableList<AccessNode>) {
                any.edges?.let { dst += it }
            }
        }
    }

    private class FinalTrees {
        var edges: AccessNode? = null
            private set
        private var edgesDelta: AccessNode? = null

        fun add(element: AccessNode): Boolean {
            val currentEdges = edges
            if (currentEdges == null) {
                edges = element
                edgesDelta = element
                return true
            }

            val (modifiedEdges, modificationDelta) = currentEdges.mergeAddDelta(element)
            if (modificationDelta == null) return false

            edges = modifiedEdges
            edgesDelta = edgesDelta?.mergeAdd(modificationDelta) ?: modificationDelta
            return true
        }

        fun getAndResetDelta(delta: MutableList<AccessNode>) {
            delta += edgesDelta ?: return
            edgesDelta = null
        }
    }
}
