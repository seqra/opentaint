package org.opentaint.ir.impl.python.protoToFlat.cfg

import org.opentaint.ir.api.python.PIRPhysicalLocation
import org.opentaint.ir.impl.python.flat.FlatBlock
import org.opentaint.ir.impl.python.flat.FlatBranch
import org.opentaint.ir.impl.python.flat.FlatCFG
import org.opentaint.ir.impl.python.flat.FlatGoto
import org.opentaint.ir.impl.python.flat.FlatInst
import org.opentaint.ir.impl.python.flat.FlatLocal
import org.opentaint.ir.impl.python.flat.FlatNextIter
import org.opentaint.ir.impl.python.flat.FlatRaise
import org.opentaint.ir.impl.python.flat.FlatReturn
import org.opentaint.ir.impl.python.flat.FlatUnreachable
import org.opentaint.ir.impl.python.flat.FlatValue
import org.opentaint.ir.impl.python.protoToFlat.ImportManager
import org.opentaint.ir.impl.python.protoToFlat.ModuleContext
import org.opentaint.ir.impl.python.protoToFlat.Scope

internal class CfgSession(
    val module: ModuleContext,
    val scope: Scope = Scope(),
    val currentFunctionQualifiedName: String? = null,
    val currentFunctionName: String? = null,
    val imports: ImportManager = module.imports,
    val constructorSelf: FlatValue? = null,
) {
    private val blocks = mutableListOf<FlatBlock>()
    private var currentInstructions = mutableListOf<FlatInst>()
    private var currentLabel = 0
    private var blockCounter = 0

    private val exceptionHandlerStack = ArrayDeque<List<Int>>()

    private val loopStack = ArrayDeque<LoopTargets>()

    private data class LoopTargets(val breakBlock: Int, val continueBlock: Int)

    private val _nonlocalNames = mutableSetOf<String>()
    private val _globalNames = mutableSetOf<String>()

    fun recordNonlocal(names: Iterable<String>) {
        _nonlocalNames.addAll(names)
    }

    fun recordGlobal(names: Iterable<String>) {
        _globalNames.addAll(names)
    }

    val nonlocalNames: Set<String> get() = _nonlocalNames
    val globalNames: Set<String> get() = _globalNames

    fun newBlock(): Int = ++blockCounter

    fun activate(label: Int) {
        finalizeCurrentBlock()
        currentLabel = label
        currentInstructions = mutableListOf()
    }

    private fun finalizeCurrentBlock() {
        if (currentInstructions.isNotEmpty() || currentLabel == 0) {
            blocks.add(
                FlatBlock(
                    label = currentLabel,
                    instructions = currentInstructions.toList(),
                    exceptionHandlers = exceptionHandlerStack.lastOrNull().orEmpty(),
                )
            )
        }
    }

    fun closeCurrentBlock() {
        finalizeCurrentBlock()
        currentInstructions = mutableListOf()
    }

    fun currentBlockTerminated(): Boolean {
        val last = currentInstructions.lastOrNull() ?: return false
        return last is FlatGoto || last is FlatBranch || last is FlatReturn ||
                last is FlatRaise || last is FlatUnreachable || last is FlatNextIter
    }

    fun emit(inst: FlatInst) {
        currentInstructions.add(inst)
    }

    fun emitGoto(target: Int, location: PIRPhysicalLocation? = null) =
        emit(FlatGoto(target, location))

    fun emitGotoIfOpen(target: Int, location: PIRPhysicalLocation? = null) {
        if (!currentBlockTerminated()) emitGoto(target, location)
    }

    fun emitBranch(
        condition: FlatValue,
        trueBlock: Int,
        falseBlock: Int,
        location: PIRPhysicalLocation? = null,
    ) = emit(FlatBranch(condition, trueBlock, falseBlock, location))

    fun emitReturn(value: FlatValue?, location: PIRPhysicalLocation? = null) =
        // hack: emit `return self` at the end of the __init__
        emit(FlatReturn(value ?: constructorSelf, location))

    fun newTempValue(): FlatLocal = FlatLocal(scope.newTemp())

    inline fun <R> withExceptionHandlers(handlers: List<Int>, block: () -> R): R {
        pushExceptionHandlers(handlers)
        try {
            return block()
        } finally {
            popExceptionHandlers()
        }
    }

    fun pushExceptionHandlers(handlers: List<Int>) {
        exceptionHandlerStack.addLast(handlers)
    }

    fun popExceptionHandlers() {
        exceptionHandlerStack.removeLast()
    }

    inline fun <R> withLoopTargets(breakBlock: Int, continueBlock: Int, block: () -> R): R {
        pushLoopTargets(breakBlock, continueBlock)
        try {
            return block()
        } finally {
            popLoopTargets()
        }
    }

    fun pushLoopTargets(breakBlock: Int, continueBlock: Int) {
        loopStack.addLast(LoopTargets(breakBlock, continueBlock))
    }

    fun popLoopTargets() {
        loopStack.removeLast()
    }

    val breakTarget: Int? get() = loopStack.lastOrNull()?.breakBlock
    val continueTarget: Int? get() = loopStack.lastOrNull()?.continueBlock

    fun finalizeCfg(): FlatCFG {
        finalizeCurrentBlock()

        val exitLabels = blocks.mapNotNull { block ->
            val last = block.instructions.lastOrNull()
            if (last is FlatReturn || last is FlatRaise || last is FlatUnreachable) block.label else null
        }

        return FlatCFG(
            blocks = blocks.toList(),
            entryBlock = 0,
            exitBlocks = exitLabels,
        )
    }
}
