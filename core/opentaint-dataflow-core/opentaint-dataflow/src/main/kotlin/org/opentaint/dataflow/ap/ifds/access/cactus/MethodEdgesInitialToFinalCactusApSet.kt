package org.opentaint.dataflow.ap.ifds.access.cactus

import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSet
import org.opentaint.dataflow.ap.ifds.access.FactDemandState
import org.opentaint.dataflow.ap.ifds.access.AnyFieldCleanerEffects
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
        CactusInitialAccess(null, AnyFieldCleanerEffects.Empty)

    private inner class TaintedFactAccessEdgeStorage :
        ApStorage<CactusInitialAccess, CactusFinalAccess> {
        val sameInitialAccessEdges =
            Object2ObjectOpenHashMap<AccessPathWithCycles.AccessNode?, EdgeNonUniverseExclusionMergingStorage>()

        override fun add(
            statement: CommonInst,
            initial: CactusInitialAccess,
            final: AccessWithState<CactusFinalAccess>
        ): AccessWithState<CactusFinalAccess>? {
            check(initial.cleanerEffects == final.access.cleanerEffects)
            val storage = sameInitialAccessEdges.getOrPut(initial.access) {
                EdgeNonUniverseExclusionMergingStorage(maxInstIdx, languageManager)
            }

            return storage.add(statement, final)
        }

        override fun filter(
            dst: MutableList<Pair<CactusInitialAccess, AccessWithState<CactusFinalAccess>>>,
            statement: CommonInst,
            finalPattern: CactusInitialAccess,
        ) {
            sameInitialAccessEdges.forEach { (initialNode, storage) ->
                collectToListWithPostProcess(
                    dst,
                    { storage.allApAtStatement(it, statement) },
                    {
                        CactusInitialAccess(
                            initialNode,
                            it.access.cleanerEffects,
                        ) to it
                    }
                )
            }
        }

        override fun filter(
            dst: MutableList<AccessWithState<CactusFinalAccess>>,
            statement: CommonInst,
            initial: CactusInitialAccess,
            finalPattern: CactusInitialAccess,
        ) {
            val storage = sameInitialAccessEdges[initial.access] ?: return
            storage.allApAtStatement(dst, statement)
        }
    }

    private class EdgeNonUniverseExclusionMergingStorage(
        maxInstIdx: Int, private val languageManager: LanguageManager
    ) {
        private val demandStates = arrayOfNulls<FactDemandState>(MethodAnalyzerEdges.instructionStorageSize(maxInstIdx))
        private val edges = arrayOfNulls<CactusFinalAccess>(MethodAnalyzerEdges.instructionStorageSize(maxInstIdx))

        fun add(
            statement: CommonInst,
            accessWithState: AccessWithState<CactusFinalAccess>,
        ): AccessWithState<CactusFinalAccess>? {
            val edgeSetIdx = MethodAnalyzerEdges.instructionStorageIdx(statement, languageManager)
            val currentState = demandStates[edgeSetIdx]

            if (currentState == null) {
                demandStates[edgeSetIdx] = accessWithState.demandState
                edges[edgeSetIdx] = accessWithState.access
                return accessWithState
            }

            val currentAccess = edges[edgeSetIdx]!!
            val mergedState = currentState join accessWithState.demandState
            demandStates[edgeSetIdx] = mergedState

            val mergedAccess = currentAccess.mergeAdd(accessWithState.access)
            if (mergedAccess === currentAccess) {
                if (mergedState === currentState) return null

                return AccessWithState(mergedAccess, mergedState)
            }

            edges[edgeSetIdx] = mergedAccess
            return AccessWithState(mergedAccess, mergedState)
        }

        fun allApAtStatement(dst: MutableList<AccessWithState<CactusFinalAccess>>, statement: CommonInst) {
            val edgeSetIdx = MethodAnalyzerEdges.instructionStorageIdx(statement, languageManager)
            val demandState = demandStates[edgeSetIdx] ?: return
            val access = edges[edgeSetIdx] ?: return
            dst += AccessWithState(access, demandState)
        }
    }
}
