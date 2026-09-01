package org.opentaint.dataflow.python

import org.opentaint.dataflow.python.graph.PIRApplicationGraph
import org.opentaint.ir.api.python.PIRAssign
import org.opentaint.ir.api.python.PIRBindFunctionExpr
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRClass
import org.opentaint.ir.api.python.PIRClassType
import org.opentaint.ir.api.python.PIRDictExpr
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRGlobalNameRef
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.ir.api.python.PIRListExpr
import org.opentaint.ir.api.python.PIRLoadAttr
import org.opentaint.ir.api.python.PIRLocal
import org.opentaint.ir.api.python.PIRModuleNameRef
import org.opentaint.ir.api.python.PIRParameterRef
import org.opentaint.ir.api.python.PIRReadNameExpr
import org.opentaint.ir.api.python.PIRSetExpr
import org.opentaint.ir.api.python.PIRStringExpr
import org.opentaint.ir.api.python.PIRTupleExpr
import org.opentaint.ir.api.python.PIRType
import org.opentaint.ir.api.python.PIRUnionType
import org.opentaint.ir.api.python.PythonNames
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

    override fun initialBindings(inst: PIRInstruction): List<LocalBinding> {
        return when (inst) {
            is PIRAssign -> {
                val names = when (val rhv = inst.expr) {
                    is PIRParameterRef -> classQns(rhv.type)
                        .map { NameEntry.GlobalRef(it) }
                        .ifEmpty { listOf(NameEntry.ParamRef(rhv.index)) }

                    is PIRBindFunctionExpr -> listOf(NameEntry.GlobalRef(rhv.function.qualifiedName))

                    is PIRReadNameExpr -> when (val ref = rhv.ref) {
                        is PIRGlobalNameRef -> listOf(NameEntry.GlobalRef(ref.qualifiedName))
                        is PIRModuleNameRef -> listOf(NameEntry.GlobalRef(ref.module))
                    }

                    is PIRListExpr -> listOf(NameEntry.GlobalRef(BUILTIN_LIST))
                    is PIRTupleExpr -> listOf(NameEntry.GlobalRef(BUILTIN_TUPLE))
                    is PIRSetExpr -> listOf(NameEntry.GlobalRef(BUILTIN_SET))
                    is PIRDictExpr -> listOf(NameEntry.GlobalRef(BUILTIN_DICT))
                    is PIRStringExpr -> listOf(NameEntry.GlobalRef(BUILTIN_STR))

                    else -> emptyList()
                }
                names.map { LocalBinding(inst.target.index, it) }
            }

            is PIRCall -> {
                val resolved = inst.resolvedCallee ?: return emptyList()
                saveCallResult(inst, NameEntry.GlobalRef(resolved))

                val targetIdx = inst.target?.index ?: return emptyList()
                resultTypeQns(resolved).map { LocalBinding(targetIdx, NameEntry.GlobalRef(it)) }
            }

            else -> emptyList()
        }
    }

    override fun transfer(inst: PIRInstruction, payload: LocalBinding): List<LocalBinding> = buildList {
        val idx = payload.idx

        when (inst) {
            is PIRLoadAttr -> {
                val targetIdx = inst.target.index
                val objIdx = (inst.obj as? PIRLocal)?.index

                if (objIdx == idx) {
                    val baseName = payload.name.flattenOrNull()
                    val baseType = baseName?.let { cp.findClassOrNull(it) }
                    val chainedName = payload.name.prependSegment(inst.attribute)

                    if (baseType != null) {
                        attributeTypeQns(baseType, inst.attribute).forEach { this += LocalBinding(targetIdx, NameEntry.GlobalRef(it)) }
                        attributeMethodQn(baseType, inst.attribute)?.let { this += LocalBinding(targetIdx, NameEntry.GlobalRef(it)) }
                    } else {
                        chainedName?.let { this += LocalBinding(targetIdx, chainedName) }
                    }

                    chainedName?.let { saveResult(inst, it) }
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
                    saveCallResult(inst, payload.name)

                    if (targetIdx != null) {
                        val qn = payload.name.flattenOrNull()
                        qn?.let { resultTypeQns(it) }.orEmpty().forEach {
                            this += LocalBinding(targetIdx, NameEntry.GlobalRef(it))
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

    private fun classQns(type: PIRType?): List<String> = when (type) {
        is PIRClassType -> listOfNotNull(type.qualifiedName.ifEmpty { null })
        is PIRUnionType -> type.members.flatMap { classQns(it) }
        else -> emptyList()
    }

    private fun attributeMethodQn(baseType: PIRClass, attribute: String): String? {
        for (qn in baseType.mro) {
            val cls = cp.findClassOrNull(qn) ?: continue
            val method = cls.methods.find { it.name == attribute } ?: continue
            return method.qualifiedName
        }
        return null
    }

    private fun attributeTypeQns(baseType: PIRClass, attribute: String): List<String> {
        for (qn in baseType.mro) {
            val cls = cp.findClassOrNull(qn) ?: continue
            val attrType = cls.fields.find { it.name == attribute }?.type
                ?: cls.properties.find { it.name == attribute }?.type
                ?: continue
            return classQns(attrType)
        }
        return emptyList()
    }

    private fun resultTypeQns(calleeQn: String): List<String> {
        if (cp.findClassOrNull(calleeQn) != null) return listOf(calleeQn)
        return classQns(cp.findFunctionOrNull(calleeQn)?.returnType)
    }

    private fun saveCallResult(inst: PIRInstruction, calleeName: NameEntry) {
        val initQn = constructorInitQnOrNull(calleeName)
        if (initQn != null) {
            saveResult(inst, NameEntry.GlobalRef(initQn))
        } else {
            saveResult(inst, calleeName)
        }
    }

    private fun constructorInitQnOrNull(calleeName: NameEntry): String? {
        val qn = calleeName.flattenOrNull() ?: return null
        if (cp.findClassOrNull(qn) == null) return null
        val initQn = "$qn.${PythonNames.INIT_METHOD}"
        return if (cp.findFunctionOrNull(initQn) != null) initQn else null
    }

    private fun saveResult(inst: PIRInstruction, nameEntry: NameEntry) {
        val qfName = nameEntry.flattenOrNull() ?: return

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

        private const val BUILTIN_LIST = "builtins.list"
        private const val BUILTIN_TUPLE = "builtins.tuple"
        private const val BUILTIN_SET = "builtins.set"
        private const val BUILTIN_DICT = "builtins.dict"
        private const val BUILTIN_STR = "builtins.str"

        fun compute(method: PIRFunction, applicationGraph: PIRApplicationGraph) =
            PIRMethodQFNameReconstructor(method, applicationGraph).compute()
    }
}
