package org.opentaint.ir.test.python.tier3

import org.opentaint.ir.api.python.*
import org.opentaint.ir.impl.python.transforms.closure.ClosureRuntime

class PIRReconstructor {

    private var currentEmittedFuncNames: Set<String> = emptySet()

    private var closureBearingNames: Set<String> = emptySet()

    fun reconstruct(func: PIRFunction): String {
        currentEmittedFuncNames = emptySet()
        closureBearingNames = if (isClosureBearing(func)) setOf(func.name) else emptySet()
        return MODULE_PRELUDE + reconstructSingle(func)
    }

    private fun reconstructAdapterClass(cls: PIRClass): String {
        val sb = StringBuilder()
        val sanitizedClassName = sanitizeFuncName(cls.name)
        sb.appendLine("class $sanitizedClassName:")
        for (method in cls.methods) {
            val paramList = method.parameters.joinToString(", ") { p ->
                val pname = sanitizeLocal(p.name)
                when (p.kind) {
                    PIRParameterKind.VAR_POSITIONAL -> "*$pname"
                    PIRParameterKind.VAR_KEYWORD -> "**$pname"
                    PIRParameterKind.KEYWORD_ONLY -> pname
                    PIRParameterKind.POSITIONAL_OR_KEYWORD,
                    PIRParameterKind.POSITIONAL_ONLY -> pname
                }
            }
            sb.appendLine("    def ${method.name}($paramList):")
            // Each method has a tiny CFG built by the rewriter — emit its instructions
            // directly with 8-space indent. The IR injects `return self` into `__init__`
            // to model constructor semantics for the analysis; that's a TypeError in a real
            // constructor, so drop returns when emitting `__init__`.
            val isCtor = method.name == "__init__"
            var emittedBody = false
            for (block in method.cfg.blocks) {
                for (inst in block.instructions) {
                    if (isCtor && inst is PIRReturn) continue
                    for (line in reconstructInstruction(inst)) {
                        sb.appendLine("        $line")
                        emittedBody = true
                    }
                }
            }
            if (!emittedBody) sb.appendLine("        pass")
        }
        return sb.toString()
    }

    fun reconstructWithLambdas(func: PIRFunction, cp: PIRClasspath): String {
        val sb = StringBuilder()
        sb.append(MODULE_PRELUDE)

        val emittedFuncNames = mutableSetOf<String>()
        val closureBearingFuncs = mutableSetOf<String>()
        val resolvedFuncs = mutableListOf<PIRFunction>()
        val seen = mutableSetOf<String>()
        val queue = ArrayDeque<PIRFunction>()
        queue.addAll(
            collectLambdaRefs(func, func.module.name).mapNotNull { resolveLambda(it, cp, func.module.name) }
        )
        while (queue.isNotEmpty()) {
            val nested = queue.removeFirst()
            if (!seen.add(nested.name)) continue
            resolvedFuncs.add(nested)
            emittedFuncNames.add(nested.name)
            if (isClosureBearing(nested)) {
                closureBearingFuncs.add(nested.name)
            }
            for (ref in collectLambdaRefs(nested, func.module.name)) {
                if (ref !in seen) {
                    resolveLambda(ref, cp, func.module.name)?.let { queue.add(it) }
                }
            }
        }

        val moduleClasses = func.module.classes.filter { it.name.startsWith("<closure_") }
        for (cls in moduleClasses) {
            for (method in cls.methods) {
                val readNames = method.cfg.instList
                    .filterIsInstance<PIRAssign>()
                    .mapNotNull { a ->
                        val ref = (a.expr as? PIRReadNameExpr)?.ref as? PIRGlobalNameRef ?: return@mapNotNull null
                        a.target.index to ref.qualifiedName
                    }.toMap()
                for (inst in method.cfg.instList) {
                    if (inst is PIRCall) {
                        val callee = inst.callee as? PIRLocalVar ?: continue
                        val qn = readNames[callee.index] ?: continue
                        val calleeShort = qn.substringAfterLast('.')
                        if (calleeShort.startsWith("<closure_") && calleeShort.endsWith("_impl>")) {
                            if (calleeShort !in seen) {
                                val implFn = cp.modules.flatMap { it.functions }.firstOrNull { it.name == calleeShort }
                                if (implFn != null) {
                                    seen.add(implFn.name)
                                    resolvedFuncs.add(implFn)
                                    emittedFuncNames.add(implFn.name)
                                    if (isClosureBearing(implFn)) {
                                        closureBearingFuncs.add(implFn.name)
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        for (cls in moduleClasses) {
            sb.append(reconstructAdapterClass(cls))
            sb.appendLine()
        }

        closureBearingNames = closureBearingFuncs
        for (lambdaFunc in resolvedFuncs) {
            sb.append(reconstructSingle(lambdaFunc, emittedFuncNames))
            sb.appendLine()
        }

        sb.append(reconstructSingle(func, emittedFuncNames))
        closureBearingNames = emptySet()
        return sb.toString()
    }

    private fun isClosureBearing(func: PIRFunction): Boolean {
        val hasSelf = func.parameters.firstOrNull()?.name == SELF_PARAM_RAW
        if (!hasSelf) return false
        val n = func.name
        if (n.startsWith("<closure_") && n.endsWith("_impl>")) return false
        return true
    }

    private fun resolveLambda(name: String, cp: PIRClasspath, moduleName: String): PIRFunction? {
        cp.findFunctionOrNull("$moduleName.$name")?.let { return it }
        for (mod in cp.modules) {
            mod.functions.find { it.name == name }?.let { return it }
        }
        return null
    }

    companion object {
        private const val SELF_PARAM_RAW = ClosureRuntime.SELF_PARAM_NAME

        private const val SELF_PARAM_SAFE = "__self__"

        private const val MODULE_PRELUDE = """class __pir_cell__:
    pass

def _closure_class(f):
    class _Wrapper:
        def __call__(self, *args, **kwargs):
            return f(self, *args, **kwargs)
    return _Wrapper

"""
    }

    private fun reconstructSingle(
        func: PIRFunction,
        emittedFuncNames: Set<String> = emptySet(),
    ): String {
        currentEmittedFuncNames = emittedFuncNames
        val sb = StringBuilder()

        val paramNames = func.parameters.map { it.name }.toSet()

        val params = func.parameters.joinToString(", ") { p ->
            val pname = sanitizeLocal(p.name)
            if (p.hasDefault && p.defaultValue != null) {
                "$pname=${val_(p.defaultValue!!)}"
            } else {
                pname
            }
        }
        if (isClosureBearing(func)) {
            sb.appendLine("@_closure_class")
        }
        sb.appendLine("def ${sanitizeFuncName(func.name)}($params):")

        val blocks = func.cfg.blocks
        if (blocks.isEmpty()) {
            sb.appendLine("    pass")
            return sb.toString()
        }

        val locals = mutableSetOf<String>()
        for (inst in func.instList) {
            collectLocals(inst, locals)
        }
        locals.removeAll(paramNames)
        locals.removeAll(emittedFuncNames)
        locals.remove("")

        for (local in locals.sorted()) {
            sb.appendLine("    ${sanitizeLocal(local)} = None")
        }

        val blockByLabel = blocks.associateBy { it.label }

        sb.appendLine("    __state = ${blocks.first().label}")
        sb.appendLine("    while True:")

        for (block in blocks) {
            val hasHandlers = block.exceptionHandlers.isNotEmpty()
            val handlerLabel = if (hasHandlers) block.exceptionHandlers.first() else -1

            sb.appendLine("        if __state == ${block.label}:")
            if (block.instructions.isEmpty()) {
                sb.appendLine("            pass")
                continue
            }

            if (hasHandlers) {
                sb.appendLine("            try:")
                for (inst in block.instructions) {
                    val lines = reconstructInstruction(inst)
                    for (line in lines) {
                        sb.appendLine("                $line")
                    }
                }
                sb.appendLine("            except:")
                sb.appendLine("                __state = $handlerLabel")
                sb.appendLine("                continue")
            } else {
                for (inst in block.instructions) {
                    val lines = reconstructInstruction(inst)
                    for (line in lines) {
                        sb.appendLine("            $line")
                    }
                }
            }
        }

        return sb.toString()
    }

    private fun collectLambdaRefs(func: PIRFunction, moduleName: String = ""): Set<String> {
        val refs = mutableSetOf<String>()
        fun addQn(qn: String) {
            val short = qn.substringAfterLast('.')
            val module = qn.substringBeforeLast('.', "")
            if (short.startsWith("<lambda>")) refs.add(short)
            else if (module == moduleName) refs.add(short)
        }
        for (inst in func.instList) {
            if (inst !is PIRAssign) continue
            when (val expr = inst.expr) {
                is PIRReadNameExpr -> (expr.ref as? PIRGlobalNameRef)?.let { addQn(it.qualifiedName) }
                is PIRBindFunctionExpr -> addQn(expr.function.qualifiedName)
                else -> {}
            }
        }
        return refs
    }

    private fun reconstructInstruction(inst: PIRInstruction): List<String> {
        return when (inst) {
            is PIRAssign -> reconstructAssign(inst)
            is PIRLoadAttr -> listOf("${val_(inst.target)} = ${val_(inst.obj)}.${inst.attribute}")
            is PIRCall -> {
                val args = inst.args.joinToString(", ") { callArg(it) }
                val call = "${val_(inst.callee)}($args)"
                val t = inst.target
                if (t != null) listOf("${val_(t)} = $call")
                else listOf(call)
            }
            is PIRStoreAttr -> listOf("${val_(inst.obj)}.${inst.attribute} = ${val_(inst.value)}")
            is PIRStoreSubscript -> listOf("${val_(inst.obj)}[${val_(inst.index)}] = ${val_(inst.value)}")
            is PIRStoreGlobal -> listOf("${inst.ref.qualifiedName.substringAfterLast('.')} = ${val_(inst.value)}")
            is PIRStoreClosure -> listOf("${inst.name} = ${val_(inst.value)}")
            is PIRNextIter -> listOf(
                "try:",
                "    ${val_(inst.target)} = next(${val_(inst.iterator)})",
                "    __state = ${inst.bodyBlock}",
                "except StopIteration:",
                "    __state = ${inst.exitBlock}",
                "continue",
            )
            is PIRUnpack -> {
                val targets = inst.targets.joinToString(", ") { val_(it) }
                listOf("$targets = ${val_(inst.source)}")
            }
            is PIRGoto -> listOf("__state = ${inst.targetBlock}", "continue")
            is PIRBranch -> listOf(
                "if ${val_(inst.condition)}:",
                "    __state = ${inst.trueBlock}",
                "else:",
                "    __state = ${inst.falseBlock}",
                "continue",
            )
            is PIRReturn -> {
                if (inst.value != null) listOf("return ${val_(inst.value!!)}")
                else listOf("return None")
            }
            is PIRRaise -> {
                if (inst.exception != null) listOf("raise ${val_(inst.exception!!)}")
                else listOf("raise")
            }
            is PIRExceptHandler -> {
                if (inst.target != null) listOf("# except handler -> ${val_(inst.target!!)}")
                else listOf("# except handler")
            }
            is PIRYield -> {
                if (inst.value != null) {
                    if (inst.target != null)
                        listOf("${val_(inst.target!!)} = (yield ${val_(inst.value!!)})")
                    else listOf("yield ${val_(inst.value!!)}")
                } else {
                    if (inst.target != null) listOf("${val_(inst.target!!)} = (yield)")
                    else listOf("yield")
                }
            }
            is PIRYieldFrom -> {
                if (inst.target != null)
                    listOf("${val_(inst.target!!)} = (yield from ${val_(inst.iterable)})")
                else listOf("yield from ${val_(inst.iterable)}")
            }
            is PIRAwait -> {
                if (inst.target != null)
                    listOf("${val_(inst.target!!)} = await ${val_(inst.awaitable)}")
                else listOf("await ${val_(inst.awaitable)}")
            }
            is PIRDeleteLocal -> listOf("del ${val_(inst.local)}")
            is PIRDeleteAttr -> listOf("del ${val_(inst.obj)}.${inst.attribute}")
            is PIRDeleteSubscript -> listOf("del ${val_(inst.obj)}[${val_(inst.index)}]")
            is PIRDeleteGlobal -> listOf("del ${inst.ref.qualifiedName.substringAfterLast('.')}")
            is PIRUnreachable -> listOf("raise RuntimeError('unreachable')")
        }
    }

    private fun reconstructAssign(inst: PIRAssign): List<String> {
        val target = val_(inst.target)
        val exprLines = when (val expr = inst.expr) {
            is PIRBinaryExpr -> listOf("$target = ${val_(expr.left)} ${binOp(expr)} ${val_(expr.right)}")
            is PIRUnaryExpr -> listOf("$target = ${unaryOp(expr)}${val_(expr.operand)}")
            is PIRCompareExpr -> listOf("$target = ${val_(expr.left)} ${cmpOp(expr)} ${val_(expr.right)}")
            is PIRSubscriptExpr -> listOf("$target = ${val_(expr.obj)}[${val_(expr.index)}]")
            is PIRListExpr -> {
                val elems = expr.elements.joinToString(", ") { val_(it) }
                listOf("$target = [$elems]")
            }
            is PIRTupleExpr -> {
                val elems = expr.elements.joinToString(", ") { val_(it) }
                listOf("$target = ($elems,)")
            }
            is PIRSetExpr -> {
                val elems = expr.elements.joinToString(", ") { val_(it) }
                if (elems.isEmpty()) listOf("$target = set()")
                else listOf("$target = {$elems}")
            }
            is PIRDictExpr -> {
                val pairs = expr.keys.zip(expr.values).joinToString(", ") { (k, v) ->
                    "${val_(k)}: ${val_(v)}"
                }
                listOf("$target = {$pairs}")
            }
            is PIRSliceExpr -> {
                val lo = expr.lower?.let { val_(it) } ?: ""
                val hi = expr.upper?.let { val_(it) } ?: ""
                val st = expr.step?.let { ":${val_(it)}" } ?: ""
                if (expr.obj != null) listOf("$target = ${val_(expr.obj!!)}[$lo:$hi$st]")
                else listOf("$target = slice(${lo.ifEmpty { "None" }}, ${hi.ifEmpty { "None" }}, ${expr.step?.let { val_(it) } ?: "None"})")
            }
            is PIRStringExpr -> {
                val parts = expr.parts.joinToString(" + ") { "str(${val_(it)})" }
                listOf("$target = $parts")
            }
            is PIRIterExpr -> listOf("$target = iter(${val_(expr.iterable)})")
            is PIRTypeCheckExpr -> listOf("$target = isinstance(${val_(expr.value)}, object)")
            is PIRBindFunctionExpr -> {
                val fnName = expr.function.qualifiedName.substringAfterLast('.')
                if (fnName in closureBearingNames) {
                    return listOf("$target = ${sanitizeFuncName(fnName)}()")
                }
                val tgtLocal = inst.target as? PIRLocalVar
                val isSelfAssign = tgtLocal != null
                    && fnName == tgtLocal.name
                    && fnName in currentEmittedFuncNames
                if (isSelfAssign) return emptyList()
                listOf("$target = ${sanitizeFuncName(fnName)}")
            }
            is PIRReadNameExpr -> {
                val name = when (val ref = expr.ref) {
                    is PIRGlobalNameRef -> sanitizeFuncName(ref.qualifiedName.substringAfterLast('.'))
                    is PIRModuleNameRef -> ref.module
                }
                listOf("$target = $name")
            }
            is PIRValue -> listOf("$target = ${val_(expr)}")
        }
        return exprLines
    }

    private fun val_(v: PIRValue): String {
        return when (v) {
            is PIRLocalVar -> sanitizeLocal(v.name)
            is PIRParameterRef -> sanitizeLocal(v.name)
            is PIRIntConst -> v.value.toString()
            is PIRFloatConst -> v.value.toString()
            is PIRStrConst -> "\"${v.value.replace("\\", "\\\\").replace("\"", "\\\"")}\""
            is PIRBoolConst -> if (v.value) "True" else "False"
            is PIRNoneConst -> "None"
            is PIREllipsisConst -> "..."
            is PIRBytesConst -> "b\"...\""
            is PIRComplexConst -> "complex(${v.real}, ${v.imag})"
        }
    }

    private fun sanitizeLocal(name: String): String {
        if (name == SELF_PARAM_RAW) return SELF_PARAM_SAFE
        return name
            .replace("\$", "__")
            .replace("<", "__")
            .replace(">", "__")
    }

    private fun sanitizeFuncName(name: String): String {
        return name
            .replace("<", "__")
            .replace(">", "__")
            .replace("\$", "_")
    }

    private fun binOp(expr: PIRBinaryExpr): String = when (expr) {
        is PIRAddExpr -> "+"
        is PIRSubExpr -> "-"
        is PIRMulExpr -> "*"
        is PIRDivExpr -> "/"
        is PIRFloorDivExpr -> "//"
        is PIRModExpr -> "%"
        is PIRPowExpr -> "**"
        is PIRMatMulExpr -> "@"
        is PIRBitAndExpr -> "&"
        is PIRBitOrExpr -> "|"
        is PIRBitXorExpr -> "^"
        is PIRLShiftExpr -> "<<"
        is PIRRShiftExpr -> ">>"
    }

    private fun unaryOp(expr: PIRUnaryExpr): String = when (expr) {
        is PIRNegExpr -> "-"
        is PIRPosExpr -> "+"
        is PIRNotExpr -> "not "
        is PIRInvertExpr -> "~"
    }

    private fun cmpOp(expr: PIRCompareExpr): String = when (expr) {
        is PIREqExpr -> "=="
        is PIRNeExpr -> "!="
        is PIRLtExpr -> "<"
        is PIRLeExpr -> "<="
        is PIRGtExpr -> ">"
        is PIRGeExpr -> ">="
        is PIRIsExpr -> "is"
        is PIRIsNotExpr -> "is not"
        is PIRInExpr -> "in"
        is PIRNotInExpr -> "not in"
    }

    private fun callArg(arg: PIRCallArg): String = when (arg.kind) {
        PIRCallArgKind.POSITIONAL -> val_(arg.value)
        PIRCallArgKind.KEYWORD -> "${arg.keyword}=${val_(arg.value)}"
        PIRCallArgKind.STAR -> "*${val_(arg.value)}"
        PIRCallArgKind.DOUBLE_STAR -> "**${val_(arg.value)}"
    }

    private fun collectLocals(inst: PIRInstruction, locals: MutableSet<String>) {
        fun collectExprLocals(expr: PIRExpr) {
            when (expr) {
                is PIRBinaryExpr -> { collectLocalFromValue(expr.left, locals); collectLocalFromValue(expr.right, locals) }
                is PIRUnaryExpr -> collectLocalFromValue(expr.operand, locals)
                is PIRCompareExpr -> { collectLocalFromValue(expr.left, locals); collectLocalFromValue(expr.right, locals) }
                is PIRSubscriptExpr -> { collectLocalFromValue(expr.obj, locals); collectLocalFromValue(expr.index, locals) }
                is PIRListExpr -> expr.elements.forEach { collectLocalFromValue(it, locals) }
                is PIRTupleExpr -> expr.elements.forEach { collectLocalFromValue(it, locals) }
                is PIRSetExpr -> expr.elements.forEach { collectLocalFromValue(it, locals) }
                is PIRDictExpr -> { expr.keys.forEach { collectLocalFromValue(it, locals) }; expr.values.forEach { collectLocalFromValue(it, locals) } }
                is PIRSliceExpr -> { expr.obj?.let { collectLocalFromValue(it, locals) }; expr.lower?.let { collectLocalFromValue(it, locals) }; expr.upper?.let { collectLocalFromValue(it, locals) }; expr.step?.let { collectLocalFromValue(it, locals) } }
                is PIRStringExpr -> expr.parts.forEach { collectLocalFromValue(it, locals) }
                is PIRIterExpr -> collectLocalFromValue(expr.iterable, locals)
                is PIRTypeCheckExpr -> collectLocalFromValue(expr.value, locals)
                is PIRBindFunctionExpr -> {}
                is PIRReadNameExpr -> {}
                is PIRValue -> collectLocalFromValue(expr, locals)
            }
        }
        when (inst) {
            is PIRAssign -> { collectLocalFromValue(inst.target, locals); collectExprLocals(inst.expr) }
            is PIRLoadAttr -> { collectLocalFromValue(inst.target, locals); collectLocalFromValue(inst.obj, locals) }
            is PIRCall -> { inst.target?.let { collectLocalFromValue(it, locals) }; collectLocalFromValue(inst.callee, locals) }
            is PIRStoreAttr -> { collectLocalFromValue(inst.obj, locals); collectLocalFromValue(inst.value, locals) }
            is PIRStoreSubscript -> { collectLocalFromValue(inst.obj, locals); collectLocalFromValue(inst.index, locals); collectLocalFromValue(inst.value, locals) }
            is PIRStoreGlobal -> collectLocalFromValue(inst.value, locals)
            is PIRStoreClosure -> collectLocalFromValue(inst.value, locals)
            is PIRNextIter -> { collectLocalFromValue(inst.target, locals); collectLocalFromValue(inst.iterator, locals) }
            is PIRUnpack -> { inst.targets.forEach { collectLocalFromValue(it, locals) }; collectLocalFromValue(inst.source, locals) }
            is PIRBranch -> collectLocalFromValue(inst.condition, locals)
            is PIRReturn -> inst.value?.let { collectLocalFromValue(it, locals) }
            is PIRRaise -> inst.exception?.let { collectLocalFromValue(it, locals) }
            is PIRExceptHandler -> inst.target?.let { collectLocalFromValue(it, locals) }
            is PIRYield -> { inst.target?.let { collectLocalFromValue(it, locals) }; inst.value?.let { collectLocalFromValue(it, locals) } }
            is PIRYieldFrom -> { inst.target?.let { collectLocalFromValue(it, locals) }; collectLocalFromValue(inst.iterable, locals) }
            is PIRAwait -> { inst.target?.let { collectLocalFromValue(it, locals) }; collectLocalFromValue(inst.awaitable, locals) }
            is PIRDeleteLocal -> collectLocalFromValue(inst.local, locals)
            is PIRDeleteAttr -> collectLocalFromValue(inst.obj, locals)
            is PIRDeleteSubscript -> { collectLocalFromValue(inst.obj, locals); collectLocalFromValue(inst.index, locals) }
            is PIRGoto, is PIRDeleteGlobal, is PIRUnreachable -> {}
        }
    }

    private fun collectLocalFromValue(v: PIRValue, locals: MutableSet<String>) {
        if (v is PIRLocalVar) locals.add(v.name)
    }
}
