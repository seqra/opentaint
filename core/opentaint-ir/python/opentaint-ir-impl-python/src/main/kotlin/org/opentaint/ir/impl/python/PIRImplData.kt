package org.opentaint.ir.impl.python

import org.opentaint.ir.api.python.PIRBasicBlock
import org.opentaint.ir.api.python.PIRBranchingInst
import org.opentaint.ir.api.python.PIRCFG
import org.opentaint.ir.api.python.PIRClass
import org.opentaint.ir.api.python.PIRDecorator
import org.opentaint.ir.api.python.PIRDiagnostic
import org.opentaint.ir.api.python.PIRField
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.ir.api.python.PIRModule
import org.opentaint.ir.api.python.PIRParameter
import org.opentaint.ir.api.python.PIRParameterKind
import org.opentaint.ir.api.python.PIRProperty
import org.opentaint.ir.api.python.PIRTerminatingInst
import org.opentaint.ir.api.python.PIRType
import org.opentaint.ir.api.python.PIRValue


data class PIRModuleImpl(
    override val name: String,
    override val path: String,
    override val classes: List<PIRClass>,
    override val functions: List<PIRFunction>,
    override val fields: List<PIRField>,
    override val moduleInit: PIRFunction,
    override val diagnostics: List<PIRDiagnostic> = emptyList(),
) : PIRModule {
    override fun equals(other: Any?): Boolean = this === other || (other is PIRModuleImpl && name == other.name && path == other.path)
    override fun hashCode(): Int = name.hashCode() * 31 + path.hashCode()
    override fun toString(): String = "PIRModule($name)"
}

class PIRClassImpl(
    override val name: String,
    override val qualifiedName: String,
    override val baseClasses: List<String>,
    override val mro: List<String>,
    override val methods: List<PIRFunction>,
    override val fields: List<PIRField>,
    override val nestedClasses: List<PIRClass>,
    override val properties: List<PIRProperty>,
    override val decorators: List<PIRDecorator>,
    override val isAbstract: Boolean,
    override val isDataclass: Boolean,
    override val isEnum: Boolean,
) : PIRClass {
    override lateinit var module: PIRModule

    override fun equals(other: Any?): Boolean = this === other || (other is PIRClassImpl && qualifiedName == other.qualifiedName)
    override fun hashCode(): Int = qualifiedName.hashCode()
    override fun toString(): String = "PIRClass($qualifiedName)"
}

class PIRFunctionImpl(
    override val name: String,
    override val qualifiedName: String,
    override val parameters: List<PIRParameter>,
    override val returnType: PIRType,
    override val cfg: PIRCFG,
    override val decorators: List<PIRDecorator>,
    override val isAsync: Boolean,
    override val isGenerator: Boolean,
    override val isStaticMethod: Boolean,
    override val isClassMethod: Boolean,
    override val isProperty: Boolean,
    override val closureVars: List<String>,
    override var enclosingClass: PIRClass?,
) : PIRFunction {
    override lateinit var module: PIRModule

    override val instList: List<PIRInstruction> get() = cfg.instList

    override fun equals(other: Any?): Boolean = this === other || (other is PIRFunctionImpl && qualifiedName == other.qualifiedName)
    override fun hashCode(): Int = qualifiedName.hashCode()
    override fun toString(): String = "PIRFunction($qualifiedName)"
}

data class PIRParameterImpl(
    override val name: String,
    override val type: PIRType,
    override val kind: PIRParameterKind,
    override val hasDefault: Boolean,
    override val defaultValue: PIRValue? = null,
    override val index: Int,
) : PIRParameter

data class PIRFieldImpl(
    override val name: String,
    override val type: PIRType,
    override val isClassVar: Boolean,
) : PIRField

data class PIRPropertyImpl(
    override val name: String,
    override val type: PIRType,
    override val getter: PIRFunction?,
    override val setter: PIRFunction?,
    override val deleter: PIRFunction?,
) : PIRProperty

data class PIRDecoratorImpl(
    override val name: String,
    override val qualifiedName: String,
    override val arguments: List<String>,
) : PIRDecorator

class PIRCFGImpl(
    override val blocks: List<PIRBasicBlock>,
    override val instList: List<PIRInstruction>,
    private val entryLabel: Int,
    private val exitLabels: Set<Int>,
    private val instToBlock: List<Int>,
) : PIRCFG {
    private val blocksByLabel = blocks.associateBy { it.label }

    override val entry: PIRInstruction
        get() = instList.first()

    override val exits: Set<PIRInstruction>
        get() = exitLabels.mapNotNullTo(hashSetOf()) { block(it).instructions.lastOrNull() }

    override val entryBlock: PIRBasicBlock
        get() = blocksByLabel[entryLabel] ?: blocks.first()

    override val exitBlocks: Set<PIRBasicBlock>
        get() = exitLabels.mapTo(hashSetOf()) { block(it) }

    override fun successors(inst: PIRInstruction): List<PIRInstruction> =
        when (inst) {
            is PIRBranchingInst -> inst.successors.map { instList[it] }
            is PIRTerminatingInst -> emptyList()
            else -> instList.getOrNull(inst.location.index + 1)?.let { listOf(it) }
                ?: error("Unexpected non-terminating last instruction: $inst")
        }

    override fun successors(block: PIRBasicBlock): List<PIRBasicBlock> {
        val last = block.instructions.lastOrNull() ?: return emptyList()
        return when (last) {
            is PIRBranchingInst -> last.blockSuccessors.map { block(it) }
            is PIRTerminatingInst -> emptyList()
            else -> error("Unexpected block last instruction: $last")
        }
    }

    override fun predecessors(block: PIRBasicBlock): List<PIRBasicBlock> {
        return blocks.filter { block in successors(it) }
    }

    override fun predecessors(inst: PIRInstruction): List<PIRInstruction> {
        return instList.filter { inst in successors(it) }
    }

    override fun exceptionalSuccessors(block: PIRBasicBlock): List<PIRBasicBlock> {
        return block.exceptionHandlers.mapNotNull { blocksByLabel[it] }
    }

    override fun block(label: Int): PIRBasicBlock {
        return blocksByLabel[label] ?: throw IllegalArgumentException("No block with label $label")
    }

    override fun block(inst: PIRInstruction): PIRBasicBlock {
        return block(instToBlock[inst.location.index])
    }

    companion object {
        val EMPTY_CFG = PIRCFGImpl(emptyList(), emptyList(), 0, emptySet(), emptyList())
    }
}
