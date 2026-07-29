package org.opentaint.dataflow.ap.ifds.access.cactus

import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSet
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.util.collectToListWithPostProcess
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodEdgesInitialToFinalCactusApSet(
    methodInitialStatement: CommonInst,
    private val maxInstIdx: Int,
    private val languageManager: LanguageManager
) : CommonF2FSet<CactusInitialAccess, CactusFinalAccess>(methodInitialStatement),
    CactusInitialApAccess, CactusFinalApAccess {
    override fun createApStorage(): ApStorage<CactusInitialAccess, CactusFinalAccess> =
        TaintedFactAccessEdgeStorage()

    override fun mostAbstractPattern(base: AccessPathBase): CactusInitialAccess =
        null

    private inner class TaintedFactAccessEdgeStorage :
        ApStorage<CactusInitialAccess, CactusFinalAccess> {
        val sameInitialAccessEdges =
            Object2ObjectOpenHashMap<AccessPathWithCycles.AccessNode?, EdgeNonUniverseExclusionMergingStorage>()

        override fun add(
            statement: CommonInst,
            initial: CactusInitialAccess,
            final: AccessWithExclusion<CactusFinalAccess>
        ): AccessWithExclusion<CactusFinalAccess>? {
            val storage = sameInitialAccessEdges.getOrPut(initial) {
                EdgeNonUniverseExclusionMergingStorage(maxInstIdx, languageManager)
            }

            return storage.add(statement, final)
        }

        override fun filter(
            dst: MutableList<Pair<CactusInitialAccess, AccessWithExclusion<CactusFinalAccess>>>,
            statement: CommonInst,
            finalPattern: CactusInitialAccess,
        ) {
            sameInitialAccessEdges.forEach { (initialNode, storage) ->
                collectToListWithPostProcess(
                    dst,
                    { storage.allApAtStatement(it, statement) },
                    { initialNode to it }
                )
            }
        }

        override fun filter(
            dst: MutableList<AccessWithExclusion<CactusFinalAccess>>,
            statement: CommonInst,
            initial: CactusInitialAccess,
            finalPattern: CactusInitialAccess,
        ) {
            val storage = sameInitialAccessEdges[initial] ?: return
            storage.allApAtStatement(dst, statement)
        }
    }

    private class EdgeNonUniverseExclusionMergingStorage(
        maxInstIdx: Int, private val languageManager: LanguageManager
    ) {
        private val exclusions = arrayOfNulls<ExclusionSet>(MethodAnalyzerEdges.instructionStorageSize(maxInstIdx))
        private val edges = arrayOfNulls<CactusFinalAccess>(MethodAnalyzerEdges.instructionStorageSize(maxInstIdx))

        fun add(
            statement: CommonInst,
            accessWithState: AccessWithExclusion<CactusFinalAccess>,
        ): AccessWithExclusion<CactusFinalAccess>? {
            val edgeSetIdx = MethodAnalyzerEdges.instructionStorageIdx(statement, languageManager)
            val currentState = exclusions[edgeSetIdx]

            if (currentState == null) {
                exclusions[edgeSetIdx] = accessWithState.exclusion
                edges[edgeSetIdx] = accessWithState.access
                return accessWithState
            }

            val currentAccess = edges[edgeSetIdx]!!
            val mergedState = currentState.union(accessWithState.exclusion)
            exclusions[edgeSetIdx] = mergedState

            val mergedAccess = currentAccess.mergeAdd(accessWithState.access)
            if (mergedAccess === currentAccess) {
                if (mergedState === currentState) return null

                return AccessWithExclusion(mergedAccess, mergedState)
            }

            edges[edgeSetIdx] = mergedAccess
            return AccessWithExclusion(mergedAccess, mergedState)
        }

        fun allApAtStatement(dst: MutableList<AccessWithExclusion<CactusFinalAccess>>, statement: CommonInst) {
            val edgeSetIdx = MethodAnalyzerEdges.instructionStorageIdx(statement, languageManager)
            val exclusion = exclusions[edgeSetIdx] ?: return
            val access = edges[edgeSetIdx] ?: return
            dst += AccessWithExclusion(access, exclusion)
        }
    }
}
