package org.opentaint.ir.impl.python.protoToFlat

import org.opentaint.ir.impl.python.flat.FlatBlock
import org.opentaint.ir.impl.python.flat.FlatCFG
import org.opentaint.ir.impl.python.flat.FlatCall
import org.opentaint.ir.impl.python.flat.FlatClass
import org.opentaint.ir.impl.python.flat.FlatFunctionIR
import org.opentaint.ir.impl.python.flat.FlatModuleIR

/**
 * Rewrites `resolvedCallee` from mypy's dotted qualified name for a nested def (`m.outer.inner`)
 * into the lifter's `$`-scoped encoding (`m.outer$inner`)
 */
internal object ResolvedCalleeNormalizer {

    fun normalize(module: FlatModuleIR): FlatModuleIR {
        val knownQns = collectQualifiedNames(module)

        fun normalizeCfg(cfg: FlatCFG): FlatCFG {
            val newBlocks = cfg.blocks.map { block ->
                val newInstructions = block.instructions.map { inst ->
                    if (inst is FlatCall) inst.copy(resolvedCallee = remap(inst.resolvedCallee, knownQns))
                    else inst
                }
                FlatBlock(block.label, newInstructions, block.exceptionHandlers)
            }
            return cfg.copy(blocks = newBlocks)
        }

        fun normalizeFunction(fn: FlatFunctionIR): FlatFunctionIR =
            fn.copy(cfg = normalizeCfg(fn.cfg))

        fun normalizeClass(cls: FlatClass): FlatClass = cls.copy(
            methods = cls.methods.map(::normalizeFunction),
            nestedClasses = cls.nestedClasses.map(::normalizeClass),
        )

        return module.copy(
            functions = module.functions.map(::normalizeFunction),
            moduleInit = normalizeFunction(module.moduleInit),
            classes = module.classes.map(::normalizeClass),
        )
    }

    private fun collectQualifiedNames(module: FlatModuleIR): Set<String> {
        val out = HashSet<String>()
        out.add(module.moduleInit.qualifiedName)
        for (fn in module.functions) out.add(fn.qualifiedName)
        for (cls in module.classes) collectClassQns(cls, out)
        return out
    }

    private fun collectClassQns(cls: FlatClass, out: MutableSet<String>) {
        out.add(cls.qualifiedName)
        for (m in cls.methods) out.add(m.qualifiedName)
        for (nested in cls.nestedClasses) collectClassQns(nested, out)
    }

    private fun remap(original: String?, knownQns: Set<String>): String? {
        if (original == null) return null
        if (original in knownQns) return original
        var current: String = original
        while (true) {
            val lastDot = current.lastIndexOf('.')
            if (lastDot <= 0) return original
            val candidate = current.substring(0, lastDot) + "\$" + current.substring(lastDot + 1)
            if (candidate in knownQns) return candidate
            current = candidate
        }
    }
}
