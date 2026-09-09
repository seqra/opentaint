package org.opentaint.ir.impl.python.transforms.closure

import org.opentaint.ir.api.python.PIRPhysicalLocation
import org.opentaint.ir.impl.python.flat.FlatAnyType
import org.opentaint.ir.impl.python.flat.FlatBindFunction
import org.opentaint.ir.impl.python.flat.FlatBuildDict
import org.opentaint.ir.impl.python.flat.FlatCall
import org.opentaint.ir.impl.python.flat.FlatCallArg
import org.opentaint.ir.impl.python.flat.FlatClass
import org.opentaint.ir.impl.python.flat.FlatDeleteAttr
import org.opentaint.ir.impl.python.flat.FlatDeleteLocal
import org.opentaint.ir.impl.python.flat.FlatFunctionIR
import org.opentaint.ir.impl.python.flat.FlatGlobalNameRef
import org.opentaint.ir.impl.python.flat.FlatInst
import org.opentaint.ir.impl.python.flat.FlatReadName
import org.opentaint.ir.impl.python.flat.FlatLoadAttr
import org.opentaint.ir.impl.python.flat.FlatLoadSubscript
import org.opentaint.ir.impl.python.flat.FlatLocal
import org.opentaint.ir.impl.python.flat.FlatNextIter
import org.opentaint.ir.impl.python.flat.FlatParamKind
import org.opentaint.ir.impl.python.flat.FlatParameter
import org.opentaint.ir.impl.python.flat.FlatParameterRef
import org.opentaint.ir.impl.python.flat.FlatStoreAttr
import org.opentaint.ir.impl.python.flat.FlatStrConst
import org.opentaint.ir.impl.python.flat.FlatValue
import org.opentaint.ir.impl.python.flat.mapOperand
import org.opentaint.ir.impl.python.flat.mapTarget

internal data class RewriteOutput(
    val impl: FlatFunctionIR,
    val adapterClass: FlatClass? = null,
)

internal class ClosureRewriteLimitation(message: String) : RuntimeException(message)

internal class RewriteCtx(
    private val fn: FlatFunctionIR,
    private val ci: ClosureInfo,
    private val info: Map<String, ClosureInfo>,
    private val moduleName: String,
) {
    private val ownedCells: Set<String> = ci.cellVars
    private val receivedCells: Set<String> = ci.closureVars
    private val cellLocals: Map<String, FlatLocal> = buildMap {
        for (n in ownedCells) this[n] = FlatLocal(ClosureRuntime.cellLocalName(n))
        for (n in receivedCells) this[n] = FlatLocal(ClosureRuntime.cellLocalName(n))
    }
    private val originalParamNames: Set<String> = fn.parameters.map { it.name }.toSet()
    private var tempCounter: Int = 0
    private val envLocal: FlatLocal = FlatLocal(ClosureRuntime.ENV_LOCAL_NAME)
    private val blockPrologues: MutableMap<Int, MutableList<FlatInst>> = mutableMapOf()

    init {
        for (paramName in originalParamNames) {
            check(paramName != ClosureRuntime.ENV_LOCAL_NAME) {
                "Closure rewrite reserved name '${ClosureRuntime.ENV_LOCAL_NAME}' collides with " +
                    "parameter of ${fn.qualifiedName}"
            }
            check(!paramName.startsWith(ClosureRuntime.CELL_LOCAL_PREFIX)) {
                "Closure rewrite reserved prefix '${ClosureRuntime.CELL_LOCAL_PREFIX}' collides " +
                    "with parameter '$paramName' of ${fn.qualifiedName}"
            }
        }
    }

    fun run(): RewriteOutput {
        val isCapturing = ci.closureVars.isNotEmpty()
        val newParameters = if (isCapturing) {
            listOf(selfParameter()) + fn.parameters
        } else {
            fn.parameters
        }

        addBlockPrologue(fn.cfg.entryBlock, buildPrologue())

        val rewrittenBlocks = fn.cfg.blocks.map { block ->
            block to block.instructions.flatMap { rewriteInstruction(it) }
        }

        val newBlocks = rewrittenBlocks.map { (block, rewrittenBody) ->
            block.copy(instructions = blockPrologues[block.label].orEmpty() + rewrittenBody)
        }

        val newCfg = fn.cfg.copy(blocks = newBlocks)

        val rebuiltImpl = if (isCapturing) {
            val implQn = ClosureRuntime.implFunctionQn(moduleName, fn.name)
            fn.copy(
                name = implQn.substringAfterLast('.'),
                qualifiedName = implQn,
                parameters = newParameters,
                closureVars = ci.closureVars,
                cfg = newCfg,
            )
        } else {
            fn.copy(
                parameters = newParameters,
                closureVars = ci.closureVars,
                cfg = newCfg,
            )
        }

        val adapter = if (isCapturing) buildAdapterClass(fn, moduleName) else null

        return RewriteOutput(impl = rebuiltImpl, adapterClass = adapter)
    }

    private fun buildPrologue(): List<FlatInst> = buildList {
        for (name in ownedCells) {
            val cellLocal = cellLocals.getValue(name)
            val callee = freshTemp()
            add(
                FlatReadName(
                    target = callee,
                    ref = FlatGlobalNameRef("builtins.${ClosureRuntime.CELL_CLASS_NAME}"),
                ),
            )
            add(
                FlatCall(
                    target = cellLocal,
                    callee = callee,
                    args = emptyList(),
                ),
            )
        }
        if (receivedCells.isNotEmpty()) {
            add(
                FlatLoadAttr(
                    target = envLocal,
                    obj = FlatParameterRef(ClosureRuntime.SELF_PARAM_NAME),
                    attribute = ClosureRuntime.ENV_ATTR_NAME,
                ),
            )
            for (name in receivedCells) {
                add(
                    FlatLoadSubscript(
                        target = cellLocals.getValue(name),
                        obj = envLocal,
                        index = FlatStrConst(name),
                    ),
                )
            }
        }
    }

    private fun isCellManaged(name: String): Boolean = name in cellLocals

    private fun freshTemp(): FlatLocal = FlatLocal("\$tc${tempCounter++}")

    private fun loadOperand(
        value: FlatValue,
        location: PIRPhysicalLocation?,
        into: MutableList<FlatInst>,
    ): FlatValue {
        if (value !is FlatLocal || !isCellManaged(value.name)) return value
        val tmp = freshTemp()
        into += FlatLoadAttr(
            target = tmp,
            obj = cellLocals.getValue(value.name),
            attribute = ClosureRuntime.CELL_VALUE_ATTR_NAME,
            physicalLocation = location,
        )
        return tmp
    }

    private fun redirectTarget(
        target: FlatValue,
        location: PIRPhysicalLocation?,
        into: MutableList<FlatInst>,
    ): FlatValue {
        if (target !is FlatLocal || !isCellManaged(target.name)) return target
        val tmp = freshTemp()
        into += FlatStoreAttr(
            obj = cellLocals.getValue(target.name),
            attribute = ClosureRuntime.CELL_VALUE_ATTR_NAME,
            value = tmp,
            physicalLocation = location,
        )
        return tmp
    }

    private fun rewriteInstruction(inst: FlatInst): List<FlatInst> = when (inst) {
        is FlatBindFunction -> rewriteBind(inst)
        is FlatDeleteLocal -> rewriteDeleteLocal(inst)
        is FlatNextIter -> rewriteNextIter(inst)
        else -> defaultRewrite(inst)
    }

    private fun defaultRewrite(inst: FlatInst): List<FlatInst> {
        val pre = ArrayList<FlatInst>()
        val post = ArrayList<FlatInst>()
        val core = inst
            .mapOperand { v -> loadOperand(v, inst.physicalLocation, pre) }
            .mapTarget { t -> redirectTarget(t, inst.physicalLocation, post) }
        return pre + core + post
    }

    private fun rewriteNextIter(inst: FlatNextIter): List<FlatInst> {
        val pre = ArrayList<FlatInst>()
        val store = ArrayList<FlatInst>()
        val core = inst
            .mapOperand { v -> loadOperand(v, inst.physicalLocation, pre) }
            .mapTarget { t -> redirectTarget(t, inst.physicalLocation, store) }
        addBlockPrologue(inst.bodyBlock, store)
        return pre + core
    }

    private fun addBlockPrologue(label: Int, instructions: List<FlatInst>) {
        if (instructions.isEmpty()) return
        blockPrologues.getOrPut(label) { mutableListOf() } += instructions
    }

    private fun rewriteDeleteLocal(inst: FlatDeleteLocal): List<FlatInst> {
        val l = inst.local as? FlatLocal ?: return listOf(inst)
        if (!isCellManaged(l.name)) return listOf(inst)

        return listOf(
            FlatDeleteAttr(
                obj = cellLocals.getValue(l.name),
                attribute = ClosureRuntime.CELL_VALUE_ATTR_NAME,
                physicalLocation = inst.physicalLocation,
            ),
        )
    }

    private fun rewriteBind(inst: FlatBindFunction): List<FlatInst> {
        val location = inst.physicalLocation
        val childQn = inst.function.qualifiedName
        val childClosureVars = info[childQn]?.closureVars.orEmpty()

        if (childClosureVars.isEmpty()) return defaultRewrite(inst)

        val childAdapterQn = ClosureRuntime.adapterClassQn(
            moduleName = moduleName,
            fnName = childQn.substringAfterLast('.'),
        )

        val pre = ArrayList<FlatInst>()
        val post = ArrayList<FlatInst>()

        val (envBuildInst, envValueLocal) = buildEnvDict(childClosureVars, location)
        pre += envBuildInst

        val callTarget = redirectTarget(inst.target, location, post)

        val adapterLocal = freshTemp()
        pre += FlatReadName(
            target = adapterLocal,
            ref = FlatGlobalNameRef(childAdapterQn),
            physicalLocation = location,
        )

        val core = FlatCall(
            target = callTarget,
            callee = adapterLocal,
            args = listOf(FlatCallArg(envValueLocal)),
            physicalLocation = location,
        )

        return pre + core + post
    }

    private fun buildEnvDict(childClosureVars: Set<String>, location: PIRPhysicalLocation?): Pair<FlatInst, FlatLocal> {
        val keys: List<FlatValue> = childClosureVars.map { FlatStrConst(it) }
        val values: List<FlatValue> = childClosureVars.map { name ->
            cellLocals[name]
                ?: throw ClosureRewriteLimitation(
                    "Closure rewrite: child captures '$name' but parent " +
                        "${fn.qualifiedName} has no cell for it (cells: ${cellLocals.keys})",
                )
        }
        val envTarget = freshTemp()
        val envInst = FlatBuildDict(
            target = envTarget,
            keys = keys,
            values = values,
            physicalLocation = location,
        )
        return envInst to envTarget
    }

    private companion object {
        private fun selfParameter(): FlatParameter = FlatParameter(
            name = ClosureRuntime.SELF_PARAM_NAME,
            type = FlatAnyType,
            kind = FlatParamKind.POSITIONAL_OR_KEYWORD,
            hasDefault = false,
            defaultValue = null,
        )
    }
}
