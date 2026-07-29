package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges.Companion.instructionStorageIdx
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges.Companion.instructionStorageSize
import org.opentaint.dataflow.ap.ifds.access.common.CommonZ2FSet
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodEdgesFinalAutomataApSet(
    methodInitialStatement: CommonInst,
    private val maxInstIdx: Int,
    private val languageManager: LanguageManager
) : CommonZ2FSet<AutomataFinalAccess>(methodInitialStatement), AutomataFinalApAccess {
    override fun createApStorage(): ApStorage<AutomataFinalAccess> = InstructionFactSet(maxInstIdx, languageManager)

    private class InstructionFactSet(
        maxInstIdx: Int,
        private val languageManager: LanguageManager,
    ): ApStorage<AutomataFinalAccess> {
        private val finalFacts =
            arrayOfNulls<AutomataFinalAccess>(instructionStorageSize(maxInstIdx))

        override fun addEdge(statement: CommonInst, accessPath: AutomataFinalAccess): AutomataFinalAccess? {
            val factSetIdx = instructionStorageIdx(statement, languageManager)
            val current = finalFacts[factSetIdx]
            if (current == null) {
                finalFacts[factSetIdx] = accessPath
                return accessPath
            }

            val merged = current.mergeAdd(accessPath)
            if (merged === current) return null
            finalFacts[factSetIdx] = merged
            return merged
        }

        override fun collectApAtStatement(statement: CommonInst, dst: MutableList<AutomataFinalAccess>) {
            finalFacts[instructionStorageIdx(statement, languageManager)]?.let(dst::add)
        }

        override fun toString(): String =
            "${finalFacts.indices.sumOf { finalFacts[it]?.access?.size ?: 0 }}"
    }
}
