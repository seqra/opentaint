package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.access.cactus.AccessCactus.AccessNode
import org.opentaint.dataflow.ap.ifds.access.common.CommonNDF2FSummary
import org.opentaint.dataflow.ap.ifds.access.common.ndf2f.DefaultNDF2FSummaryStorageWithAp
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodNDInitialToFinalCactusApSummariesStorage(methodEntryPoint: CommonInst) :
    CommonNDF2FSummary<CactusFinalAccess>(methodEntryPoint), CactusFinalApAccess {
    private class Builder : NDF2FBBuilder<CactusFinalAccess>(), CactusFinalApAccess

    override fun createStorage(): Storage<CactusFinalAccess> = object :
        DefaultNDF2FSummaryStorageWithAp<CactusInitialAccess, CactusFinalAccess>(methodEntryPoint),
        CactusInitialApAccess {
        override fun createBuilder(): NDF2FBBuilder<CactusFinalAccess> = Builder()

        override fun createStorage(idx: Int): Storage<CactusInitialAccess, CactusFinalAccess> = FactStorage(idx)

        private inner class FactStorage(
            override val storageIdx: Int,
        ) : Storage<CactusInitialAccess, CactusFinalAccess> {
            private var edges: CactusFinalAccess? = null
            private var edgesDelta: CactusFinalAccess? = null

            override fun add(element: CactusFinalAccess): Storage<CactusInitialAccess, CactusFinalAccess>? {
                val currentEdges = edges
                if (currentEdges == null) {
                    edges = element
                    edgesDelta = element
                    return this
                }

                val (modifiedEdges, modificationDelta) = currentEdges.mergeAddDelta(element)
                if (modificationDelta == null) return null

                edges = modifiedEdges
                edgesDelta = edgesDelta?.mergeAdd(modificationDelta) ?: modificationDelta
                return this
            }

            override fun getAndResetDelta(delta: MutableList<CactusFinalAccess>) {
                delta += edgesDelta ?: return
                edgesDelta = null
            }

            override fun collectTo(dst: MutableList<CactusFinalAccess>) {
                edges?.let { dst += it }
            }
        }
    }
}
