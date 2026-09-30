package org.opentaint.ir.impl.python.transforms

import org.opentaint.ir.impl.python.flat.FlatAssign
import org.opentaint.ir.impl.python.flat.FlatClass
import org.opentaint.ir.impl.python.flat.FlatDeleteLocal
import org.opentaint.ir.impl.python.flat.FlatFunctionIR
import org.opentaint.ir.impl.python.flat.FlatLocal
import org.opentaint.ir.impl.python.flat.FlatModuleIR
import org.opentaint.ir.impl.python.flat.FlatParameterRef
import org.opentaint.ir.impl.python.flat.FlatValue
import org.opentaint.ir.impl.python.flat.mapOperand
import org.opentaint.ir.impl.python.flat.mapTarget
import org.opentaint.ir.impl.python.flat.targets

object ParameterBinding {
    fun transform(module: FlatModuleIR): FlatModuleIR = module.copy(
        functions = module.functions.map(::bindParameters),
        moduleInit = bindParameters(module.moduleInit),
        classes = module.classes.map(::bindClass),
    )

    private fun bindClass(cls: FlatClass): FlatClass = cls.copy(
        methods = cls.methods.map(::bindParameters),
        nestedClasses = cls.nestedClasses.map(::bindClass),
    )

    private fun bindParameters(fn: FlatFunctionIR): FlatFunctionIR {
        val written = writtenParameterNames(fn)
        val copied = fn.parameters.filter { it.name in written }
        if (copied.isEmpty()) return fn

        val locals = copied.associate { it.name to FlatLocal(it.name, it.type) }
        val prologue = copied.map { FlatAssign(locals.getValue(it.name), FlatParameterRef(it.name, it.type)) }

        fun toLocal(v: FlatValue): FlatValue {
            if (v !is FlatParameterRef) return v

            return locals.getOrDefault(v.name, v)
        }

        val blocks = fn.cfg.blocks.map { block ->
            val body = block.instructions.map { it.mapOperand(::toLocal).mapTarget(::toLocal) }
            block.copy(instructions = if (block.label == fn.cfg.entryBlock) prologue + body else body)
        }
        return fn.copy(cfg = fn.cfg.copy(blocks = blocks))
    }

    private fun writtenParameterNames(fn: FlatFunctionIR): Set<String> = buildSet {
        for (block in fn.cfg.blocks) {
            for (inst in block.instructions) {
                for (target in inst.targets) if (target is FlatParameterRef) add(target.name)
                if (inst is FlatDeleteLocal) (inst.local as? FlatParameterRef)?.let { add(it.name) }
            }
        }
    }
}
