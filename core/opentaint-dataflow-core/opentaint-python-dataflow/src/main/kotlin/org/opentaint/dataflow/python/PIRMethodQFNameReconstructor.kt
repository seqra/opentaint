package org.opentaint.dataflow.python

import org.opentaint.dataflow.python.graph.PIRApplicationGraph
import org.opentaint.ir.api.python.PIRAssign
import org.opentaint.ir.api.python.PIRBindFunctionExpr
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRClassType
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRGlobalNameRef
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.ir.api.python.PIRLoadAttr
import org.opentaint.ir.api.python.PIRLocal
import org.opentaint.ir.api.python.PIRModuleNameRef
import org.opentaint.ir.api.python.PIRParameterRef
import org.opentaint.ir.api.python.PIRReadName
import org.opentaint.ir.api.python.targets

class PIRMethodQFNameReconstructor private constructor(
    method: PIRFunction,
    applicationGraph: PIRApplicationGraph,
) : PIRMethodIntraproceduralWalker<PIRMethodQFNameReconstructor.LocalBinding>(method, applicationGraph) {
    private val cp = applicationGraph.cp
    private val result = mutableMapOf<PIRInstruction, MutableSet<String>>()

    private fun compute(): Map<PIRInstruction, Set<String>> {
        walk()
        return result
    }

    override fun initialBinding(inst: PIRInstruction): LocalBinding? {
        return when (inst) {
            is PIRReadName -> {
                val name = when (val ref = inst.ref) {
                    is PIRGlobalNameRef -> NameEntry.GlobalRef(ref.qualifiedName)
                    is PIRModuleNameRef -> NameEntry.GlobalRef(ref.module)
                }
                LocalBinding(inst.target.index, name)
            }

            is PIRAssign -> when (val rhv = inst.expr) {
                is PIRParameterRef ->
                    LocalBinding(inst.target.index, NameEntry.ParamRef(rhv.index))

                is PIRBindFunctionExpr ->
                    LocalBinding(inst.target.index, NameEntry.GlobalRef(rhv.function.qualifiedName))

                else -> null
            }

            is PIRCall -> {
                val resolved = inst.resolvedCallee ?: return null
                saveResult(inst, NameEntry.GlobalRef(resolved))

                val targetIdx = inst.target?.index
                val resultQn = resultTypeQn(resolved)

                if (targetIdx != null && resultQn != null) {
                    LocalBinding(targetIdx, NameEntry.GlobalRef(resultQn))
                } else {
                    null
                }
            }

            else -> null
        }
    }

    override fun transfer(inst: PIRInstruction, payload: LocalBinding): List<LocalBinding> = buildList {
        val idx = payload.idx

        when (inst) {
            is PIRLoadAttr -> {
                val targetIdx = inst.target.index
                val objIdx = (inst.obj as? PIRLocal)?.index

                if (objIdx == idx) {
                    val newName = payload.name.prependSegment(inst.attribute)

                    if (newName != null) {
                        this += LocalBinding(targetIdx, newName)
                        saveResult(inst, newName)
                    }
                }

                if (targetIdx != idx) {
                    this += payload
                }
            }

            is PIRAssign -> {
                val sourceIdx = (inst.expr as? PIRLocal)?.index
                val targetIdx = inst.target.index

                if (idx != targetIdx) {
                    this += payload
                }

                if (sourceIdx == idx) {
                    this += LocalBinding(targetIdx, payload.name)
                }
            }

            is PIRCall -> {
                val calleeIdx = (inst.callee as? PIRLocal)?.index
                val targetIdx = inst.target?.index

                if (calleeIdx == idx) {
                    saveResult(inst, payload.name)

                    if (targetIdx != null) {
                        val qn = payload.name.flattenOrNull()
                        val resultTypeQn = qn?.let { resultTypeQn(it) }
                        if (resultTypeQn != null) {
                            this += LocalBinding(targetIdx, NameEntry.GlobalRef(resultTypeQn))
                        }
                    }
                }

                if (targetIdx != idx) {
                    this += payload
                }
            }

            else -> {
                val idxReassignment = inst.targets.any { it.index == idx }

                if (!idxReassignment) {
                    this += payload
                }
            }
        }
    }

    private fun resultTypeQn(calleeQn: String): String? {
        if (cp.findClassOrNull(calleeQn) != null) return calleeQn
        val returnType = cp.findFunctionOrNull(calleeQn)?.returnType as? PIRClassType ?: return null
        return returnType.qualifiedName.ifEmpty { null }
    }

    private fun saveResult(inst: PIRInstruction, nameEntry: NameEntry) {
        val qfName = nameEntry.flattenOrNull() ?: return // parameters are not supported yet

        result.getOrPut(inst) { hashSetOf() }
            .add(qfName)
    }

    private fun NameEntry.flattenOrNull(): String? {
        var cur: NameEntry = this
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
                is NameEntry.ParamRef -> return null
            }
        }
        return segments.asReversed().joinToString(separator = ".")
    }

    private fun NameEntry.prependSegment(segmentName: String): NameEntry? {
        if (size >= SEGMENT_SIZE_LIMIT) return null

        return NameEntry.NameSegment(segmentName, this)
    }

    data class LocalBinding(val idx: Int, val name: NameEntry)

    sealed interface NameEntry {
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