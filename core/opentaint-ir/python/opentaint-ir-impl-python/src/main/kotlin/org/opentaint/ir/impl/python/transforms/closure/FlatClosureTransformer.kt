package org.opentaint.ir.impl.python.transforms.closure

import org.opentaint.ir.impl.python.flat.FlatModuleIR

object FlatClosureTransformer {
    fun transform(module: FlatModuleIR): FlatModuleIR {
        val analysis = ClosureAnalyzer.analyze(module)
        return ClosureRewriter.rewrite(module, analysis)
    }
}
