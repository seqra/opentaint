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
        for (n in ownedCells) this[n] = FlatLocal(cellLocalName(n))
        for (n in receivedCells) this[n] = FlatLocal(cellLocalName(n))
    }
    private val originalParamNames: Set<String> = fn.parameters.map { it.name }.toSet()
    private var tempCounter: Int = 0
    private val envLocal: FlatLocal = FlatLocal(ENV_LOCAL_NAME)

    init {
        for (paramName in originalParamNames) {
            check(paramName != ENV_LOCAL_NAME) {
                "Closure rewrite reserved name '$ENV_LOCAL_NAME' collides with " +
                    "parameter of ${fn.qualifiedName}"
            }
            check(!paramName.startsWith(CELL_LOCAL_PREFIX)) {
                "Closure rewrite reserved prefix '$CELL_LOCAL_PREFIX' collides " +
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

        val prologue = buildPrologue()

        val newBlocks = fn.cfg.blocks.map { block ->
            val rewrittenBody = block.instructions.flatMap { rewriteInstruction(it) }
            val instructions = if (block.label == fn.cfg.entryBlock) {
                prologue + rewrittenBody
            } else {
                rewrittenBody
            }
            block.copy(instructions = instructions)
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
                    ref = FlatGlobalNameRef("builtins.${ClosureRuntime.CELL_CTOR_NAME}"),
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
                    attribute = ClosureRuntime.CLOSURE_ATTR_NAME,
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

    private fun freshTemp(): FlatLocal = FlatLocal("\$tc\$${tempCounter++}")

    private fun loadOperand(value: FlatValue, location: PIRPhysicalLocation?, scope: InstRewriterScope): FlatValue {
        if (value !is FlatLocal || !isCellManaged(value.name)) return value
        val tmp = freshTemp()
        scope.emitBefore(
            FlatLoadAttr(
                target = tmp,
                obj = cellLocals.getValue(value.name),
                attribute = ClosureRuntime.CELL_VALUE_ATTR,
                physicalLocation = location,
            ),
        )
        return tmp
    }

    private fun redirectTarget(target: FlatValue, location: PIRPhysicalLocation?, scope: InstRewriterScope): FlatValue {
        if (target !is FlatLocal || !isCellManaged(target.name)) return target
        val tmp = freshTemp()
        scope.emitAfter(
            FlatStoreAttr(
                obj = cellLocals.getValue(target.name),
                attribute = ClosureRuntime.CELL_VALUE_ATTR,
                value = tmp,
                physicalLocation = location,
            ),
        )
        return tmp
    }

    private fun rewriteInstruction(inst: FlatInst): List<FlatInst> {
        val scope = InstRewriterScope(inst)
        when (inst) {
            is FlatBindFunction -> rewriteBind(inst, scope)
            is FlatDeleteLocal -> rewriteDeleteLocal(inst, scope)
            else -> defaultRewrite(inst, scope)
        }
        return scope.finish()
    }

    private fun defaultRewrite(inst: FlatInst, scope: InstRewriterScope) {
        val rewritten = inst
            .mapOperand { v -> loadOperand(v, inst.physicalLocation, scope) }
            .mapTarget { t -> redirectTarget(t, inst.physicalLocation, scope) }
        scope.replaceWith(rewritten)
    }

    private fun rewriteDeleteLocal(inst: FlatDeleteLocal, scope: InstRewriterScope) {
        val l = inst.local as? FlatLocal ?: return
        if (!isCellManaged(l.name)) return

        scope.replaceWith(
            FlatDeleteAttr(
                obj = cellLocals.getValue(l.name),
                attribute = ClosureRuntime.CELL_VALUE_ATTR,
                physicalLocation = inst.physicalLocation,
            ),
        )
    }

    private fun rewriteBind(inst: FlatBindFunction, scope: InstRewriterScope) {
        val location = inst.physicalLocation
        val childQn = inst.function.qualifiedName
        val childClosureVars = info[childQn]?.closureVars.orEmpty()

        if (childClosureVars.isEmpty()) {
            defaultRewrite(inst, scope)
            return
        }

        val childAdapterQn = ClosureRuntime.adapterClassQn(
            moduleName = moduleName,
            fnName = childQn.substringAfterLast('.'),
        )
        val originalTarget = inst.target

        val (envBuildInst, envValueLocal) = buildEnvDict(childClosureVars, location)
        scope.emitBefore(envBuildInst)

        val callTarget = redirectTarget(originalTarget, location, scope)

        val adapterLocal = freshTemp()
        scope.emitBefore(
            FlatReadName(
                target = adapterLocal,
                ref = FlatGlobalNameRef(childAdapterQn),
                physicalLocation = location,
            ),
        )

        scope.replaceWith(
            FlatCall(
                target = callTarget,
                callee = adapterLocal,
                args = listOf(FlatCallArg(envValueLocal)),
                physicalLocation = location,
            ),
        )
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
        private const val ENV_LOCAL_NAME = "\$env"
        private const val CELL_LOCAL_PREFIX = "\$cell\$"

        private fun cellLocalName(name: String): String = "$CELL_LOCAL_PREFIX$name"

        private fun selfParameter(): FlatParameter = FlatParameter(
            name = ClosureRuntime.SELF_PARAM_NAME,
            type = FlatAnyType,
            kind = FlatParamKind.POSITIONAL_OR_KEYWORD,
            hasDefault = false,
            defaultValue = null,
        )
    }
}
