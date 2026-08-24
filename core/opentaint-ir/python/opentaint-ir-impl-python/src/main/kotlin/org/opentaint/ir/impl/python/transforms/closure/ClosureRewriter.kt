package org.opentaint.ir.impl.python.transforms.closure

import org.opentaint.ir.api.python.PIRDiagnostic
import org.opentaint.ir.api.python.PIRDiagnosticSeverity
import org.opentaint.ir.impl.python.flat.FlatClass
import org.opentaint.ir.impl.python.flat.FlatFunctionIR
import org.opentaint.ir.impl.python.flat.FlatModuleIR

internal object ClosureRewriter {

    fun rewrite(module: FlatModuleIR, closureAnalysis: ClosureAnalysis): FlatModuleIR {
        val info = closureAnalysis.info
        val diagnostics = closureAnalysis.diagnostics.toMutableList()
        val adapterClasses = ArrayList<FlatClass>()
        val runner = RewriteRunner(module.moduleName, info, diagnostics)

        val newFunctions = module.functions.map {
            val out = runner.rewriteFunction(it)
            out.adapterClass?.let(adapterClasses::add)
            out.impl
        }
        val newModuleInit = runner.rewriteFunction(module.moduleInit).also {
            it.adapterClass?.let(adapterClasses::add)
        }.impl
        val newClasses = module.classes.map { runner.rewriteClass(it, adapterClasses) }

        return module.copy(
            functions = newFunctions,
            moduleInit = newModuleInit,
            classes = newClasses + adapterClasses,
            diagnostics = module.diagnostics + diagnostics,
        )
    }
}

private class RewriteRunner(
    private val moduleName: String,
    private val info: Map<String, ClosureInfo>,
    private val diagnostics: MutableList<PIRDiagnostic>,
) {

    fun rewriteClass(
        cls: FlatClass,
        adapterAccumulator: MutableList<FlatClass>,
    ): FlatClass = cls.copy(
        methods = cls.methods.map {
            val out = rewriteFunction(it)
            out.adapterClass?.let(adapterAccumulator::add)
            out.impl
        },
        nestedClasses = cls.nestedClasses.map { rewriteClass(it, adapterAccumulator) },
    )

    fun rewriteFunction(fn: FlatFunctionIR): RewriteOutput {
        val ci = info[fn.qualifiedName] ?: return RewriteOutput(fn)

        if (ci.cellVars.isEmpty() && ci.closureVars.isEmpty()) {
            return RewriteOutput(fn)
        }

        return try {
            RewriteCtx(fn, ci, info, moduleName).run()
        } catch (e: ClosureRewriteLimitation) {
            diagnostics.add(
                PIRDiagnostic(
                    severity = PIRDiagnosticSeverity.ERROR,
                    message = "Closure rewrite failed for ${fn.qualifiedName}: ${e.message}",
                    functionName = fn.qualifiedName,
                    exceptionType = e::class.simpleName ?: "ClosureRewriteLimitation",
                ),
            )
            RewriteOutput(fn)
        }
    }
}
