package org.opentaint.dataflow.ap.ifds

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges.AbstractStaticEdges.Companion.isAbstractStaticEdge
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesInitialToFinalApSet
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.BitSet

class MethodAnalyzerEdges(
    apManager: ApManager,
    private val methodEntryPoint: MethodEntryPoint,
    languageManager: LanguageManager
) {
    var modificationVersion: Long = 0
        private set

    private val maxInstIdx = languageManager.getMaxInstIndex(methodEntryPoint.method)

    private val zeroToZeroEdges = SameInitialZeroFactEdges(maxInstIdx, languageManager)
    private val zeroToFactEdges = apManager.methodEdgesFinalApSet(methodEntryPoint.statement, maxInstIdx, languageManager)
    private val abstractStaticEdges = AbstractStaticEdges(apManager, maxInstIdx, languageManager)
    private val taintedToFactEdges = apManager.methodEdgesInitialToFinalApSet(methodEntryPoint.statement, maxInstIdx, languageManager)
    private val ndFactToFactEdges = apManager.methodEdgesNDInitialToFinalApSet(methodEntryPoint.statement, maxInstIdx, languageManager)

    fun add(edge: Edge): List<Edge> {
        check(edge.methodEntryPoint == methodEntryPoint)

        return addEdge(edge).also { added ->
            if (added.isNotEmpty()) modificationVersion++
        }
    }

    fun reachedStatements() = zeroToZeroEdges.reachedStatements()

    fun reachedStatementsWithFact(languageManager: LanguageManager): Map<CommonInst, Set<FinalFactAp>> {
        val result = hashMapOf<CommonInst, Set<FinalFactAp>>()
        for (instIdx in 0 until maxInstIdx + 1) {
            val stmt = languageManager.getInstByIndex(methodEntryPoint.method, instIdx)
            val z2f = mutableListOf<FinalFactAp>()
            val f2f = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
            val ndf2f = mutableListOf<Pair<Set<InitialFactAp>, FinalFactAp>>()

            zeroToFactEdges.collectApAtStatement(z2f, stmt)
            abstractStaticEdges.collectApAtStatement(f2f, stmt)
            taintedToFactEdges.collectApAtStatement(f2f, stmt)
            ndFactToFactEdges.collectApAtStatement(ndf2f, stmt)

            val facts = hashSetOf<FinalFactAp>()
            facts.addAll(z2f)
            f2f.mapTo(facts) { it.second }
            ndf2f.mapTo(facts) { it.second }

            if (facts.isNotEmpty()) {
                result[stmt] = facts
            }
        }
        return result
    }

    private fun addEdge(edge: Edge): List<Edge> {
        when (edge) {
            is Edge.ZeroToZero -> {
                val edgeAdded = zeroToZeroEdges.addZeroEdge(edge.statement)
                return if (edgeAdded) listOf(edge) else emptyList()
            }

            is Edge.ZeroToFact -> {
                val storage = zeroToFactEdges

                val edgeAp = edge.factAp
                val addedAp = storage.add(edge.statement, edgeAp) ?: return emptyList()

                if (addedAp === edgeAp) return listOf(edge)

                return listOf(Edge.ZeroToFact(edge.methodEntryPoint, edge.statement, addedAp))
            }

            is Edge.FactToFact -> {
                return addTaintedFactEdge(edge)
            }

            is Edge.NDFactToFact -> {
                val initial = edge.initialFacts
                val finalAp = edge.factAp

                val (addedInitial, addedFinal) = ndFactToFactEdges.add(edge.statement, initial, finalAp) ?: return emptyList()

                return listOf(
                    Edge.NDFactToFact(
                        methodEntryPoint = edge.methodEntryPoint,
                        initialFacts = addedInitial,
                        statement = edge.statement,
                        factAp = addedFinal
                    )
                )
            }
        }
    }

    private fun addTaintedFactEdge(edge: Edge.FactToFact): List<Edge.FactToFact> {
        val initialAp = edge.initialFactAp
        val finalAp = edge.factAp

        val storage = if (isAbstractStaticEdge(initialAp, finalAp)) abstractStaticEdges else taintedToFactEdges
        return storage.add(edge.statement, initialAp, finalAp).map { (addedInitial, addedFinal) ->
            if (addedInitial === initialAp && addedFinal === finalAp) {
                edge
            } else {
                Edge.FactToFact(
                    methodEntryPoint = edge.methodEntryPoint,
                    initialFactAp = addedInitial,
                    statement = edge.statement,
                    factAp = addedFinal,
                )
            }
        }
    }

    fun addFactToFactSupports(
        statement: CommonInst,
        initialFacts: Iterable<InitialFactAp>,
        finalFact: FinalFactAp,
        emitDelta: (InitialFactAp, FinalFactAp) -> Unit,
    ) {
        var changed = false
        val emit: (InitialFactAp, FinalFactAp) -> Unit = { initial, addedFinal ->
            changed = true
            emitDelta(initial, addedFinal)
        }

        if (finalFact.base is AccessPathBase.ClassStatic && finalFact.depth == 0) {
            val (abstractStatic, regular) = initialFacts.partition { isAbstractStaticEdge(it, finalFact) }
            abstractStaticEdges.addAll(statement, abstractStatic, finalFact, emit)
            taintedToFactEdges.addAll(statement, regular, finalFact, emit)
        } else {
            taintedToFactEdges.addAll(statement, initialFacts, finalFact, emit)
        }

        if (changed) modificationVersion++
    }

    fun allZeroToFactFactsAtStatement(statement: CommonInst, finalFactPattern: InitialFactAp): List<FinalFactAp> {
        val result = mutableListOf<FinalFactAp>()
        zeroToFactEdges.collectApAtStatement(result, statement, finalFactPattern)
        return result
    }

    fun allZeroToFactFactsAtStatement(statement: CommonInst): List<FinalFactAp> {
        val result = mutableListOf<FinalFactAp>()
        zeroToFactEdges.collectApAtStatement(result, statement)
        return result
    }

    fun allFactToFactFactsAtStatement(statement: CommonInst, finalFactPattern: InitialFactAp): List<Pair<InitialFactAp, FinalFactAp>> {
        val result = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        abstractStaticEdges.collectApAtStatement(result, statement, finalFactPattern)
        taintedToFactEdges.collectApAtStatement(result, statement, finalFactPattern)
        return result
    }

    fun allNDFactToFactFactsAtStatement(statement: CommonInst, finalFactPattern: InitialFactAp): List<Pair<Set<InitialFactAp>, FinalFactAp>> {
        val result = mutableListOf<Pair<Set<InitialFactAp>, FinalFactAp>>()
        ndFactToFactEdges.collectApAtStatement(result, statement, finalFactPattern)
        return result
    }

    fun allFactToFactFactsAtStatement(statement: CommonInst, initialFactAp: InitialFactAp, finalFactPattern: InitialFactAp): List<FinalFactAp> {
        val result = mutableListOf<FinalFactAp>()
        abstractStaticEdges.collectApAtStatement(result, statement, initialFactAp, finalFactPattern)
        taintedToFactEdges.collectApAtStatement(result, statement, initialFactAp, finalFactPattern)
        return result
    }

    fun allNDFactToFactFactsAtStatement(statement: CommonInst, initialFacts: Set<InitialFactAp>, finalFactPattern: InitialFactAp): List<FinalFactAp> {
        val result = mutableListOf<FinalFactAp>()
        ndFactToFactEdges.collectApAtStatement(result, statement, initialFacts, finalFactPattern)
        return result
    }


    private class SameInitialZeroFactEdges(
        maxInstIdx: Int,
        private val languageManager: LanguageManager
    ) {
        private val edges = BitSet(instructionStorageSize(maxInstIdx))

        fun addZeroEdge(statement: CommonInst): Boolean {
            val edgeIdx = instructionStorageIdx(statement, languageManager)
            if (edges.get(edgeIdx)) return false

            edges.set(edgeIdx)
            return true
        }

        fun reachedStatements(): BitSet = edges
    }

    private class AbstractStaticEdges(
        apManager: ApManager,
        maxInstIdx: Int,
        private val languageManager: LanguageManager
    ): MethodEdgesInitialToFinalApSet {
        private val initial = apManager.mostAbstractInitialAp(AccessPathBase.ClassStatic)
        private val final = apManager.mostAbstractFinalAp(AccessPathBase.ClassStatic)

        private val exclusions = arrayOfNulls<ExclusionSet>(instructionStorageSize(maxInstIdx))

        override fun add(
            statement: CommonInst,
            initialAp: InitialFactAp,
            finalAp: FinalFactAp
        ): List<Pair<InitialFactAp, FinalFactAp>> {
            val edgeIdx = instructionStorageIdx(statement, languageManager)
            val exclusion = finalAp.exclusions
            val currentExclusion = exclusions[edgeIdx]

            if (currentExclusion == null) {
                exclusions[edgeIdx] = exclusion
                return listOf(initialAp to finalAp)
            }

            val mergedExclusion = currentExclusion.union(exclusion)
            if (mergedExclusion === currentExclusion) return emptyList()

            exclusions[edgeIdx] = mergedExclusion
            return listOf(
                initialAp.replaceExclusions(mergedExclusion) to finalAp.replaceExclusions(mergedExclusion)
            )
        }

        override fun collectApAtStatement(
            collection: MutableList<Pair<InitialFactAp, FinalFactAp>>,
            statement: CommonInst
        ) {
            val exclusion = exclusionAt(statement) ?: return
            collection += initial.replaceExclusions(exclusion) to final.replaceExclusions(exclusion)
        }

        override fun collectApAtStatement(
            collection: MutableList<Pair<InitialFactAp, FinalFactAp>>,
            statement: CommonInst,
            finalFactPattern: InitialFactAp
        ) {
            if (finalFactPattern.base != AccessPathBase.ClassStatic) return
            collectApAtStatement(collection, statement)
        }

        override fun collectApAtStatement(
            collection: MutableList<FinalFactAp>,
            statement: CommonInst,
            initialAp: InitialFactAp,
            finalFactPattern: InitialFactAp
        ) {
            if (initialAp.base != AccessPathBase.ClassStatic || initialAp.depth != 0) return
            if (finalFactPattern.base != AccessPathBase.ClassStatic) return

            val exclusion = exclusionAt(statement) ?: return
            collection += final.replaceExclusions(exclusion)
        }

        private fun exclusionAt(statement: CommonInst): ExclusionSet? =
            exclusions[instructionStorageIdx(statement, languageManager)]

        companion object {
            fun isAbstractStaticEdge(initialAp: InitialFactAp, finalAp: FinalFactAp): Boolean =
                initialAp.base is AccessPathBase.ClassStatic
                        && initialAp.depth == 0
                        && finalAp.base is AccessPathBase.ClassStatic
                        && finalAp.depth == 0
        }
    }

    abstract class EdgeStorage<Storage : Any>(initialStatement: CommonInst) :
        AccessPathBaseStorage<Storage>(initialStatement) {
        private var locals: Int2ObjectOpenHashMap<Storage>? = null

        override fun getOrCreateLocal(idx: Int): Storage {
            val edges = locals ?: Int2ObjectOpenHashMap<Storage>().also { locals = it }
            return edges.getOrPut(idx) { createStorage() }
        }

        override fun findLocal(idx: Int): Storage? = locals?.get(idx)
        override fun forEachLocalValue(body: (AccessPathBase, Storage) -> Unit) {
            locals?.forEach { (idx, storage) -> body(AccessPathBase.LocalVar(idx), storage) }
        }

        private var constants: MutableMap<AccessPathBase.Constant, Storage>? = null

        override fun getOrCreateConstant(base: AccessPathBase.Constant): Storage {
            val edges = constants ?: Object2ObjectOpenHashMap<AccessPathBase.Constant, Storage>()
                .also { constants = it }

            return edges.getOrPut(base) { createStorage() }
        }

        override fun findConstant(base: AccessPathBase.Constant) = constants?.get(base)

        override fun forEachConstantValue(body: (AccessPathBase, Storage) -> Unit) {
            constants?.forEach { body(it.key, it.value) }
        }
    }

    companion object {
        fun instructionStorageSize(maxInstIdx: Int): Int = maxInstIdx + 1
        fun instructionStorageIdx(inst: CommonInst, languageManager: LanguageManager): Int =
            languageManager.getInstIndex(inst)
    }
}
