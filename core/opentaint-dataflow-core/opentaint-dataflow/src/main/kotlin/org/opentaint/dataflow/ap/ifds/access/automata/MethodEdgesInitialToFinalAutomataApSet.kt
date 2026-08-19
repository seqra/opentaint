package org.opentaint.dataflow.ap.ifds.access.automata

import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges.Companion.instructionStorageIdx
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges.Companion.instructionStorageSize
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesInitialToFinalApSet
import org.opentaint.dataflow.util.collectToListWithPostProcess

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
    ): List<Pair<InitialFactAp, FinalFactAp>> =
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
                    { AccessGraphInitialFactAp(initialBase, initialAg, it.exclusions) to it }
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
    ): List<Pair<InitialFactAp, FinalFactAp>> {
        check(initialAp.exclusions == finalAp.exclusions)

        val storage = this.storage
            .getOrCreate(initialAp.base)
            .getOrCreate(initialAp.access)

        val exclusion = initialAp.exclusions
        val update = storage.add(statement, finalAp.base, finalAp.access, exclusion)
            ?: return emptyList()
        val addedInitial = if (update.exclusion === exclusion) {
            initialAp
        } else {
            initialAp.replaceExclusions(update.exclusion)
        }
        val addedAccesses = if (update.reemitAll) {
            mutableListOf<AccessGraph>().also { storage.collectAccesses(it, statement, finalAp.base) }
        } else {
            listOf(finalAp.access)
        }

        return addedAccesses.map { access ->
            val addedFinal = if (access === finalAp.access && update.exclusion === exclusion) {
                finalAp
            } else {
                AccessGraphFinalFactAp(finalAp.base, access, update.exclusion)
            }
            addedInitial to addedFinal
        }
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
        data class Update(val exclusion: ExclusionSet, val reemitAll: Boolean)

        private val factStorage = FinalFactBaseStorage(initialStatement, maxInstIdx, languageManager)

        fun add(
            statement: CommonInst,
            finalBase: AccessPathBase,
            finalAg: AccessGraph,
            exclusion: ExclusionSet,
        ): Update? {
            val finalFactStorage = factStorage.getOrCreate(finalBase)
            val factUpdated = finalFactStorage.addFact(statement, finalAg)
            val exclusionUpdate = finalFactStorage.addExclusion(statement, exclusion)
            if (!factUpdated && !exclusionUpdate.changed) return null
            return Update(exclusionUpdate.exclusion, reemitAll = exclusionUpdate.changed)
        }

        fun collectAccesses(dst: MutableList<AccessGraph>, statement: CommonInst, finalBase: AccessPathBase) {
            factStorage.find(finalBase)?.collectTo(dst, statement)
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
            val exclusion = exclusion(statement) ?: return

            collectToListWithPostProcess(
                collection,
                { collectTo(it, statement) },
                { AccessGraphFinalFactAp(base, it, exclusion) }
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
        data class ExclusionUpdate(val exclusion: ExclusionSet, val changed: Boolean)

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

        private val exclusions = arrayOfNulls<ExclusionSet>(instructionStorageSize(maxInstIdx))

        fun addExclusion(statement: CommonInst, exclusion: ExclusionSet): ExclusionUpdate {
            val exclusionIdx = instructionStorageIdx(statement, languageManager)
            val currentExclusion = exclusions[exclusionIdx]

            if (currentExclusion == null) {
                exclusions[exclusionIdx] = exclusion
                return ExclusionUpdate(exclusion, changed = true)
            }

            val merged = currentExclusion.union(exclusion)
            if (merged === currentExclusion) {
                return ExclusionUpdate(merged, changed = false)
            }

            exclusions[exclusionIdx] = merged
            return ExclusionUpdate(merged, changed = true)
        }

        fun exclusion(statement: CommonInst): ExclusionSet? {
            val exclusionIdx = instructionStorageIdx(statement, languageManager)
            return exclusions[exclusionIdx]
        }

        override fun toString(): String = "${finalFacts.indices.sumOf { finalFacts[it]?.graphSize ?: 0 }}"
    }
}
