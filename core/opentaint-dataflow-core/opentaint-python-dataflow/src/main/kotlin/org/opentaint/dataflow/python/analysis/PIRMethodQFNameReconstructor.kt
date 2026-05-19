package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.python.graph.PIRApplicationGraph
import org.opentaint.ir.api.python.PIRAssign
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRGlobalNameRef
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.ir.api.python.PIRLoadAttr
import org.opentaint.ir.api.python.PIRLocal
import org.opentaint.ir.api.python.PIRModuleNameRef
import org.opentaint.ir.api.python.PIRParameterRef
import org.opentaint.ir.api.python.PIRReadName
import org.opentaint.ir.api.python.targets

class PIRMethodQFNameReconstructor private constructor(val method: PIRFunction, applicationGraph: PIRApplicationGraph) {
    private val graph = applicationGraph.methodGraph(method)
    private val queue = mutableListOf<Pair<PIRInstruction, NameBinding>>()
    private val storage = MutableList(method.instList.size) { hashSetOf<NameBinding>() }

    private val result = mutableMapOf<PIRInstruction, MutableSet<String>>()

    private fun compute(): Map<PIRInstruction, Set<String>> {
        graph.statements().forEach { addEntry(it, NameBinding.Empty) }

        loop()

        return result
    }

    private fun loop() {
        while (queue.isNotEmpty()) {
            val (inst, entry) = queue.removeLast()

            when (entry) {
                is NameBinding.Empty -> processEmpty(inst)?.let { propagateToSuccessors(inst, it) }
                is NameBinding.LocalBinding -> processLocalBinding(inst, entry).forEach { propagateToSuccessors(inst, it) }
            }
        }
    }

    private fun processEmpty(inst: PIRInstruction): NameBinding? =
        when (inst) {
            is PIRReadName -> {
                val name = when (val ref = inst.ref) {
                    is PIRGlobalNameRef -> NameEntry.GlobalRef(ref.qualifiedName)
                    is PIRModuleNameRef -> NameEntry.GlobalRef(ref.module)
                }
                NameBinding.LocalBinding(inst.target.index, name)
            }
            is PIRAssign -> {
                val rhv = inst.expr as? PIRParameterRef ?: return null
                NameBinding.LocalBinding(inst.target.index, NameEntry.ParamRef(rhv.index))
            }
            else -> null
        }

    private fun processLocalBinding(inst: PIRInstruction, entry: NameBinding.LocalBinding): List<NameBinding.LocalBinding> = buildList {
        val idx = entry.idx

        when (inst) {
            is PIRLoadAttr -> {
                val targetIdx = inst.target.index
                val objIdx = (inst.obj as? PIRLocal)?.index

                if (objIdx == idx) {
                    val newName = entry.name.prependSegment(inst.attribute)

                    if (newName != null) {
                        this += NameBinding.LocalBinding(targetIdx, newName)
                        saveResult(inst, newName)
                    }
                }

                if (targetIdx != idx) {
                    this += entry
                }
            }

            is PIRAssign -> {
                val sourceIdx = (inst.expr as? PIRLocal)?.index
                val targetIdx = inst.target.index

                if (idx != targetIdx) {
                    this += entry
                }

                if (sourceIdx == idx) {
                    this += NameBinding.LocalBinding(targetIdx, entry.name)
                }
            }

            else -> {
                val idxReassignment = inst.targets.any { it.index == idx }

                if (!idxReassignment) {
                    this += entry
                }

                val calleeIndex = ((inst as? PIRCall)?.callee as? PIRLocal)?.index
                if (calleeIndex == entry.idx) {
                    saveResult(inst, entry.name)
                }
            }
        }
    }

    private fun saveResult(inst: PIRInstruction, nameEntry: NameEntry) {
        var cur: NameEntry = nameEntry
        val segments = mutableListOf<String>()
        while (true) {
            when (cur) {
                is NameEntry.GlobalRef -> {
                    segments += cur.ref
                    break
                }
                is NameEntry.NameSegment -> {
                    segments += cur.segment
                    cur = cur.base
                }
                is NameEntry.ParamRef -> return // parameters are not supported yet
            }
        }

        val qfName = segments.asReversed().joinToString(separator = ".")

        result.getOrPut(inst) { hashSetOf() }
            .add(qfName)
    }

    private fun NameEntry.prependSegment(segmentName: String): NameEntry? {
        if (size >= SEGMENT_SIZE_LIMIT) return null

        return NameEntry.NameSegment(segmentName, this)
    }

    private fun propagateToSuccessors(inst: PIRInstruction, entry: NameBinding) {
        graph.successors(inst).forEach { addEntry(it, entry) }
    }

    private fun addEntry(inst: PIRInstruction, entry: NameBinding) {
        val instStorage = storage[inst.location.index]

        if (instStorage.add(entry)) {
            queue += inst to entry
        }
    }

    private sealed interface NameBinding {
        data object Empty : NameBinding

        data class LocalBinding(val idx: Int, val name: NameEntry) : NameBinding
    }

    private sealed interface NameEntry {
        val size: UInt

        data class ParamRef(val idx: Int) : NameEntry {
            override val size get() = 1u
        }
        data class GlobalRef(val ref: String) : NameEntry {
            override val size get() = 1u
        }

        data class NameSegment(val segment: String, val base: NameEntry) : NameEntry {
            override val size = base.size + 1u
        }
    }

    companion object {
        const val SEGMENT_SIZE_LIMIT = 7u

        fun compute(method: PIRFunction, applicationGraph: PIRApplicationGraph) =
            PIRMethodQFNameReconstructor(method, applicationGraph).compute()
    }
}