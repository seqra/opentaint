package org.opentaint.dataflow.ap.ifds.access.automata

import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges.Companion.instructionStorageIdx
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges.Companion.instructionStorageSize
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.FactFlowState
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesInitialToFinalApSet
import org.opentaint.dataflow.util.collectToListWithPostProcess
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodEdgesInitialToFinalAutomataApSet(
    methodInitialStatement: CommonInst,
    maxInstIdx: Int,
    languageManager: LanguageManager
) : MethodEdgesInitialToFinalApSet {
    private val storage = InitialFactBaseStorage(methodInitialStatement, maxInstIdx, languageManager)

    override fun add(
        statement: CommonInst,
        initialAp: InitialFactAp,
        finalAp: FinalFactAp
    ): Pair<InitialFactAp, FinalFactAp>? =
        add(statement, initialAp as AccessGraphInitialFactAp, finalAp as AccessGraphFinalFactAp)

    override fun collectApAtStatement(
        collection: MutableList<Pair<InitialFactAp, FinalFactAp>>,
        statement: CommonInst
    ) {
        collectApAtStatementInternal(collection, statement, finalFactPattern = null)
    }

    override fun collectApAtStatement(
        collection: MutableList<Pair<InitialFactAp, FinalFactAp>>,
        statement: CommonInst,
        finalFactPattern: InitialFactAp
    ) {
        collectApAtStatementInternal(collection, statement, finalFactPattern)
    }

    private fun collectApAtStatementInternal(
        collection: MutableList<Pair<InitialFactAp, FinalFactAp>>,
        statement: CommonInst,
        finalFactPattern: InitialFactAp?
    ) {
        storage.forEachValue { initialBase, initialFactStorage ->
            initialFactStorage.storage.forEach { (initialAg, storage) ->
                collectToListWithPostProcess(
                    collection,
                    { storage.collectTo(it, statement, finalFactPattern) },
                    {
                        AccessGraphInitialFactAp(
                            initialBase, initialAg, it.exclusions, it.deepCleanEffects
                        ) to it
                    }
                )
            }
        }
    }

    override fun collectApAtStatement(
        collection: MutableList<FinalFactAp>,
        statement: CommonInst,
        initialAp: InitialFactAp,
        finalFactPattern: InitialFactAp
    ) {
        val initialBaseStorage = storage.find(initialAp.base) ?: return
        val storage = initialBaseStorage.find((initialAp as AccessGraphInitialFactAp).access) ?: return
        storage.collectTo(collection, statement, finalFactPattern)
    }

    private fun add(
        statement: CommonInst,
        initialAp: AccessGraphInitialFactAp,
        finalAp: AccessGraphFinalFactAp
    ): Pair<InitialFactAp, FinalFactAp>? {
        check(initialAp.flowState == finalAp.flowState)

        val storage = this.storage
            .getOrCreate(initialAp.base)
            .getOrCreate(initialAp.access)

        val flowState = initialAp.flowState
        val addedState = storage.add(statement, finalAp.base, finalAp.access, flowState)

        if (addedState === flowState) return initialAp to finalAp
        if (addedState == null) return null

        val newInitial = initialAp.replaceFlowState(addedState)
        val newFinal = finalAp.replaceFlowState(addedState)
        return newInitial to newFinal
    }

    override fun toString(): String = storage.toString()

    private class InitialFactBaseStorage(
        private val initialStatement: CommonInst,
        private val maxInstIdx: Int,
        private val languageManager: LanguageManager
    ) : MethodAnalyzerEdges.EdgeStorage<InitialFactStorage>(initialStatement) {
        override fun createStorage(): InitialFactStorage = InitialFactStorage(initialStatement, maxInstIdx, languageManager)
    }

    private class InitialFactStorage(
        private val initialStatement: CommonInst,
        private val maxInstIdx: Int,
        private val languageManager: LanguageManager
    ) {
        val storage = Object2ObjectOpenHashMap<AccessGraph, Storage>()

        fun getOrCreate(initialAccess: AccessGraph): Storage = storage.getOrPut(initialAccess) {
            Storage(initialStatement, maxInstIdx, languageManager)
        }

        fun find(initialAccess: AccessGraph): Storage? = storage[initialAccess]

        override fun toString(): String = storage.toString()
    }

    private class Storage(
        initialStatement: CommonInst,
        maxInstIdx: Int,
        languageManager: LanguageManager
    ) {
        private val factStorage = FinalFactBaseStorage(initialStatement, maxInstIdx, languageManager)

        fun add(
            statement: CommonInst,
            finalBase: AccessPathBase,
            finalAg: AccessGraph,
            flowState: FactFlowState,
        ): FactFlowState? {
            val finalFactStorage = factStorage.getOrCreate(finalBase)
            val factUpdated = finalFactStorage.addFact(statement, finalAg)

            return finalFactStorage.addFlowState(
                statement, flowState, returnNullIfNotUpdated = !factUpdated
            )
        }

        fun collectTo(collection: MutableList<FinalFactAp>, statement: CommonInst, finalFactPattern: InitialFactAp?) {
            if (finalFactPattern != null) {
                val base = finalFactPattern.base
                val storage = factStorage.find(base) ?: return
                storage.collect(collection, statement, base)
            } else {
                factStorage.forEachValue { base, storage ->
                    storage.collect(collection, statement, base)
                }
            }
        }

        private fun InstructionFactStorage.collect(
            collection: MutableList<FinalFactAp>,
            statement: CommonInst,
            base: AccessPathBase,
        ) {
            val flowState = flowState(statement) ?: return

            collectToListWithPostProcess(
                collection,
                { collectTo(it, statement) },
                {
                    AccessGraphFinalFactAp(
                        base, it, flowState.exclusions, flowState.deepCleanEffects
                    )
                }
            )
        }
    }

    private class FinalFactBaseStorage(
        initialStatement: CommonInst,
        private val maxInstIdx: Int,
        private val languageManager: LanguageManager
    ) : MethodAnalyzerEdges.EdgeStorage<InstructionFactStorage>(initialStatement) {
        override fun createStorage(): InstructionFactStorage = InstructionFactStorage(maxInstIdx, languageManager)
    }

    private class InstructionFactStorage(
        maxInstIdx: Int,
        private val languageManager: LanguageManager
    ) {
        private val finalFacts = AccessGraphSetArray.create(instructionStorageSize(maxInstIdx))

        fun addFact(statement: CommonInst, final: AccessGraph): Boolean {
            val edgeSetIdx = instructionStorageIdx(statement, languageManager)
            val currentSet = finalFacts[edgeSetIdx]

            if (currentSet == null) {
                finalFacts[edgeSetIdx] = AccessGraphSet.single(final)
                return true
            }

            val modifiedFactSet = currentSet.add(final) ?: return false
            finalFacts[edgeSetIdx] = modifiedFactSet
            return true
        }

        fun collectTo(collection: MutableList<AccessGraph>, statement: CommonInst) {
            val edgeSetIdx = instructionStorageIdx(statement, languageManager)
            finalFacts[edgeSetIdx]?.toList(collection)
        }

        private val flowStates = arrayOfNulls<FactFlowState>(instructionStorageSize(maxInstIdx))

        fun addFlowState(
            statement: CommonInst,
            flowState: FactFlowState,
            returnNullIfNotUpdated: Boolean
        ): FactFlowState? {
            val stateIdx = instructionStorageIdx(statement, languageManager)
            val currentState = flowStates[stateIdx]

            if (currentState == null) {
                flowStates[stateIdx] = flowState
                return flowState
            }

            val merged = currentState join flowState
            if (merged === currentState) {
                return if (returnNullIfNotUpdated) null else merged
            }

            flowStates[stateIdx] = merged
            return merged
        }

        fun flowState(statement: CommonInst): FactFlowState? {
            val stateIdx = instructionStorageIdx(statement, languageManager)
            return flowStates[stateIdx]
        }

        override fun toString(): String = "${finalFacts.indices.sumOf { finalFacts[it]?.graphSize ?: 0 }}"
    }
}
