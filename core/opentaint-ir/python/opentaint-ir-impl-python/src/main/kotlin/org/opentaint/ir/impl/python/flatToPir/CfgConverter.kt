package org.opentaint.ir.impl.python.flatToPir

import org.opentaint.ir.api.python.PIRAssign
import org.opentaint.ir.api.python.PIRAwait
import org.opentaint.ir.api.python.PIRBasicBlock
import org.opentaint.ir.api.python.PIRBindFunctionExpr
import org.opentaint.ir.api.python.PIRBranch
import org.opentaint.ir.api.python.PIRCFG
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRCallArg
import org.opentaint.ir.api.python.PIRDeleteAttr
import org.opentaint.ir.api.python.PIRDeleteGlobal
import org.opentaint.ir.api.python.PIRDeleteLocal
import org.opentaint.ir.api.python.PIRDeleteSubscript
import org.opentaint.ir.api.python.PIRDictExpr
import org.opentaint.ir.api.python.PIRExceptHandler
import org.opentaint.ir.api.python.PIRGlobalNameRef
import org.opentaint.ir.api.python.PIRGoto
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.ir.api.python.PIRIterExpr
import org.opentaint.ir.api.python.PIRListExpr
import org.opentaint.ir.api.python.PIRLoadAttr
import org.opentaint.ir.api.python.PIRLocalVar
import org.opentaint.ir.api.python.PIRLocation
import org.opentaint.ir.api.python.PIRModuleNameRef
import org.opentaint.ir.api.python.PIRNameRef
import org.opentaint.ir.api.python.PIRNextIter
import org.opentaint.ir.api.python.PIRParameterRef
import org.opentaint.ir.api.python.PIRPhysicalLocation
import org.opentaint.ir.api.python.PIRRaise
import org.opentaint.ir.api.python.PIRReadNameExpr
import org.opentaint.ir.api.python.PIRReturn
import org.opentaint.ir.api.python.PIRSetExpr
import org.opentaint.ir.api.python.PIRSliceExpr
import org.opentaint.ir.api.python.PIRStoreAttr
import org.opentaint.ir.api.python.PIRStoreGlobal
import org.opentaint.ir.api.python.PIRStoreSubscript
import org.opentaint.ir.api.python.PIRStringExpr
import org.opentaint.ir.api.python.PIRSubscriptExpr
import org.opentaint.ir.api.python.PIRTupleExpr
import org.opentaint.ir.api.python.PIRTypeCheckExpr
import org.opentaint.ir.api.python.PIRUnpack
import org.opentaint.ir.api.python.PIRUnreachable
import org.opentaint.ir.api.python.PIRValue
import org.opentaint.ir.api.python.PIRYield
import org.opentaint.ir.api.python.PIRYieldFrom
import org.opentaint.ir.impl.python.PIRCFGImpl
import org.opentaint.ir.impl.python.PIRLocationImpl
import org.opentaint.ir.impl.python.flat.FlatAssign
import org.opentaint.ir.impl.python.flat.FlatAwait
import org.opentaint.ir.impl.python.flat.FlatBinOp
import org.opentaint.ir.impl.python.flat.FlatBindFunction
import org.opentaint.ir.impl.python.flat.FlatBlock
import org.opentaint.ir.impl.python.flat.FlatBranch
import org.opentaint.ir.impl.python.flat.FlatBuildDict
import org.opentaint.ir.impl.python.flat.FlatBuildList
import org.opentaint.ir.impl.python.flat.FlatBuildSet
import org.opentaint.ir.impl.python.flat.FlatBuildSlice
import org.opentaint.ir.impl.python.flat.FlatBuildString
import org.opentaint.ir.impl.python.flat.FlatBuildTuple
import org.opentaint.ir.impl.python.flat.FlatCFG
import org.opentaint.ir.impl.python.flat.FlatCall
import org.opentaint.ir.impl.python.flat.FlatCompare
import org.opentaint.ir.impl.python.flat.FlatConst
import org.opentaint.ir.impl.python.flat.FlatDeleteAttr
import org.opentaint.ir.impl.python.flat.FlatDeleteGlobal
import org.opentaint.ir.impl.python.flat.FlatDeleteLocal
import org.opentaint.ir.impl.python.flat.FlatDeleteSubscript
import org.opentaint.ir.impl.python.flat.FlatExceptHandler
import org.opentaint.ir.impl.python.flat.FlatGetIter
import org.opentaint.ir.impl.python.flat.FlatGlobalNameRef
import org.opentaint.ir.impl.python.flat.FlatGoto
import org.opentaint.ir.impl.python.flat.FlatInst
import org.opentaint.ir.impl.python.flat.FlatLoadAttr
import org.opentaint.ir.impl.python.flat.FlatLoadSubscript
import org.opentaint.ir.impl.python.flat.FlatLocal
import org.opentaint.ir.impl.python.flat.FlatModuleNameRef
import org.opentaint.ir.impl.python.flat.FlatNameRef
import org.opentaint.ir.impl.python.flat.FlatNextIter
import org.opentaint.ir.impl.python.flat.FlatParameter
import org.opentaint.ir.impl.python.flat.FlatParameterRef
import org.opentaint.ir.impl.python.flat.FlatRaise
import org.opentaint.ir.impl.python.flat.FlatReadName
import org.opentaint.ir.impl.python.flat.FlatReturn
import org.opentaint.ir.impl.python.flat.FlatStoreAttr
import org.opentaint.ir.impl.python.flat.FlatStoreGlobal
import org.opentaint.ir.impl.python.flat.FlatStoreSubscript
import org.opentaint.ir.impl.python.flat.FlatTypeCheck
import org.opentaint.ir.impl.python.flat.FlatUnaryOp
import org.opentaint.ir.impl.python.flat.FlatUnpack
import org.opentaint.ir.impl.python.flat.FlatUnreachable
import org.opentaint.ir.impl.python.flat.FlatValue
import org.opentaint.ir.impl.python.flat.FlatYield
import org.opentaint.ir.impl.python.flat.FlatYieldFrom

class CfgConversionResult(val cfg: PIRCFG, val locations: List<PIRLocationImpl>)

class CfgConverter private constructor(parameters: List<FlatParameter>, qualifiedName: String) {

    private val indexer = LocalIndexer(parameters, qualifiedName)

    companion object {
        fun convert(flat: FlatCFG, parameters: List<FlatParameter>, qualifiedName: String): CfgConversionResult =
            CfgConverter(parameters, qualifiedName).convert(flat)
    }

    private fun convert(flat: FlatCFG): CfgConversionResult {
        val sortedBlocks = flat.blocks.sortedBy { it.label }
        val blockStartIndex = calculateBlockToStartIdx(sortedBlocks)

        val instList = ArrayList<PIRInstruction>()
        val locations = ArrayList<PIRLocationImpl>()
        val instToBlock = ArrayList<Int>()
        for (block in sortedBlocks) {
            for (flatInst in block.instructions) {
                val loc = PIRLocationImpl(index = instList.size)
                instList.add(convertInstruction(flatInst, blockStartIndex, loc, flatInst.physicalLocation))
                locations.add(loc)
                instToBlock.add(block.label)
            }
        }

        val blocks = sortedBlocks.map { block ->
            val startIdx = blockStartIndex.getValue(block.label)
            PIRBasicBlock(
                label = block.label,
                instructions = instList.subList(startIdx, startIdx + block.instructions.size),
                exceptionHandlers = block.exceptionHandlers,
            )
        }

        val cfg = PIRCFGImpl(
            blocks = blocks,
            instList = instList,
            entryLabel = flat.entryBlock,
            exitLabels = flat.exitBlocks.toSet(),
            instToBlock = instToBlock,
        )
        return CfgConversionResult(cfg, locations)
    }

    private fun calculateBlockToStartIdx(blocks: List<FlatBlock>): Map<Int, Int> = buildMap {
        var idx = 0
        for (block in blocks) {
            this[block.label] = idx
            idx += block.instructions.size
        }
    }

    private fun v(flat: FlatValue): PIRValue = when (flat) {
        is FlatLocal -> PIRLocalVar(flat.name, TypeConverter.convert(flat.type), indexer.localIndex(flat.name))
        is FlatParameterRef -> PIRParameterRef(flat.name, TypeConverter.convert(flat.type), indexer.paramIndex(flat.name))
        is FlatConst -> ConstConverter.convert(flat)
    }

    private fun vLocalVar(flat: FlatValue): PIRLocalVar =
        v(flat) as? PIRLocalVar ?: error("Expected a local-var slot, got $flat")

    private fun convertNameRef(ref: FlatNameRef): PIRNameRef = when (ref) {
        is FlatGlobalNameRef -> PIRGlobalNameRef(ref.qualifiedName)
        is FlatModuleNameRef -> PIRModuleNameRef(ref.module)
    }

    private fun convertInstruction(
        flat: FlatInst,
        blockStartIndex: Map<Int, Int>,
        loc: PIRLocation,
        phys: PIRPhysicalLocation?,
    ): PIRInstruction = when (flat) {
        is FlatAssign -> PIRAssign(vLocalVar(flat.target), v(flat.source), loc, phys)
        is FlatReadName -> PIRAssign(vLocalVar(flat.target), PIRReadNameExpr(convertNameRef(flat.ref)), loc, phys)
        is FlatLoadAttr -> PIRLoadAttr(vLocalVar(flat.target), v(flat.obj), flat.attribute, TypeConverter.convert(flat.type), loc, phys)
        is FlatStoreAttr -> PIRStoreAttr(v(flat.obj), flat.attribute, v(flat.value), loc, phys)
        is FlatLoadSubscript -> PIRAssign(vLocalVar(flat.target), PIRSubscriptExpr(v(flat.obj), v(flat.index), TypeConverter.convert(flat.type)), loc, phys)
        is FlatStoreSubscript -> PIRStoreSubscript(v(flat.obj), v(flat.index), v(flat.value), loc, phys)
        is FlatStoreGlobal -> PIRStoreGlobal(PIRGlobalNameRef(flat.ref.qualifiedName), v(flat.value), loc, phys)
        is FlatBindFunction -> PIRAssign(
            vLocalVar(flat.target),
            PIRBindFunctionExpr(PIRGlobalNameRef(flat.function.qualifiedName)),
            loc,
            phys,
        )

        is FlatBinOp -> PIRAssign(vLocalVar(flat.target), flat.op.toPir(v(flat.left), v(flat.right)), loc, phys)
        is FlatUnaryOp -> PIRAssign(vLocalVar(flat.target), flat.op.toPir(v(flat.operand)), loc, phys)
        is FlatCompare -> PIRAssign(vLocalVar(flat.target), flat.op.toPir(v(flat.left), v(flat.right)), loc, phys)

        is FlatCall -> PIRCall(
            target = flat.target?.let { vLocalVar(it) },
            callee = v(flat.callee),
            args = flat.args.map { PIRCallArg(v(it.value), it.kind.toPir(), it.keyword) },
            resolvedCallee = flat.resolvedCallee,
            location = loc,
            physicalLocation = phys,
        )

        is FlatBuildList -> PIRAssign(vLocalVar(flat.target), PIRListExpr(flat.elements.map { v(it) }), loc, phys)
        is FlatBuildTuple -> PIRAssign(vLocalVar(flat.target), PIRTupleExpr(flat.elements.map { v(it) }), loc, phys)
        is FlatBuildSet -> PIRAssign(vLocalVar(flat.target), PIRSetExpr(flat.elements.map { v(it) }), loc, phys)
        is FlatBuildDict -> PIRAssign(vLocalVar(flat.target), PIRDictExpr(flat.keys.map { v(it) }, flat.values.map { v(it) }), loc, phys)
        is FlatBuildSlice -> PIRAssign(vLocalVar(flat.target), PIRSliceExpr(flat.obj?.let { v(it) }, flat.lower?.let { v(it) }, flat.upper?.let { v(it) }, flat.step?.let { v(it) }), loc, phys)
        is FlatBuildString -> PIRAssign(vLocalVar(flat.target), PIRStringExpr(flat.parts.map { v(it) }), loc, phys)

        is FlatGetIter -> PIRAssign(vLocalVar(flat.target), PIRIterExpr(v(flat.iterable)), loc, phys)
        is FlatNextIter -> PIRNextIter(
            vLocalVar(flat.target), v(flat.iterator), flat.bodyBlock, flat.exitBlock,
            blockStartIndex.getValue(flat.bodyBlock), blockStartIndex.getValue(flat.exitBlock),
            loc, phys,
        )
        is FlatUnpack -> PIRUnpack(flat.targets.map { vLocalVar(it) }, v(flat.source), flat.starIndex, loc, phys)

        is FlatGoto -> PIRGoto(flat.targetBlock, blockStartIndex.getValue(flat.targetBlock), loc, phys)
        is FlatBranch -> PIRBranch(
            v(flat.condition), flat.trueBlock, flat.falseBlock,
            blockStartIndex.getValue(flat.trueBlock), blockStartIndex.getValue(flat.falseBlock),
            loc, phys,
        )
        is FlatReturn -> PIRReturn(flat.value?.let { v(it) }, loc, phys)
        is FlatRaise -> PIRRaise(flat.exception?.let { v(it) }, flat.cause?.let { v(it) }, loc, phys)
        is FlatExceptHandler -> PIRExceptHandler(flat.target?.let { vLocalVar(it) }, flat.exceptionTypes.map { TypeConverter.convert(it) }, loc, phys)

        is FlatYield -> PIRYield(flat.target?.let { vLocalVar(it) }, flat.value?.let { v(it) }, loc, phys)
        is FlatYieldFrom -> PIRYieldFrom(flat.target?.let { vLocalVar(it) }, v(flat.iterable), loc, phys)
        is FlatAwait -> PIRAwait(flat.target?.let { vLocalVar(it) }, v(flat.awaitable), loc, phys)

        is FlatDeleteLocal -> PIRDeleteLocal(vLocalVar(flat.local), loc, phys)
        is FlatDeleteAttr -> PIRDeleteAttr(v(flat.obj), flat.attribute, loc, phys)
        is FlatDeleteSubscript -> PIRDeleteSubscript(v(flat.obj), v(flat.index), loc, phys)
        is FlatDeleteGlobal -> PIRDeleteGlobal(PIRGlobalNameRef(flat.ref.qualifiedName), loc, phys)

        is FlatTypeCheck -> PIRAssign(vLocalVar(flat.target), PIRTypeCheckExpr(v(flat.value), TypeConverter.convert(flat.type)), loc, phys)
        is FlatUnreachable -> PIRUnreachable
    }
}

private class LocalIndexer(parameters: List<FlatParameter>, private val qualifiedName: String) {
    private val paramIndices: Map<String, Int> =
        parameters.withIndex().associate { (i, p) -> p.name to i }
    private val localIndices: MutableMap<String, Int> = HashMap()
    private var nextLocalIndex: Int = parameters.size

    fun paramIndex(name: String): Int =
        paramIndices[name] ?: error("FlatParameterRef('$name') has no matching parameter in $qualifiedName")

    fun localIndex(name: String): Int =
        localIndices.getOrPut(name) { nextLocalIndex++ }
}
