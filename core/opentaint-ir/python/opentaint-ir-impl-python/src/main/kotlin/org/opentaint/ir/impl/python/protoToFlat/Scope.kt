package org.opentaint.ir.impl.python.protoToFlat

import org.opentaint.ir.impl.python.flat.FlatLocal
import org.opentaint.ir.impl.python.flat.FlatParameter
import org.opentaint.ir.impl.python.flat.FlatParameterRef
import org.opentaint.ir.impl.python.flat.FlatValue

internal class Scope(parameters: List<FlatParameter>) {
    private var tempCounter = 0
    private val parametersByName: Map<String, FlatParameter> = parameters.associateBy { it.name }

    fun newTemp(): String = "\$t${tempCounter++}"

    fun variable(name: String): FlatValue =
        parametersByName[name]?.let { FlatParameterRef(it.name, it.type) } ?: FlatLocal(name)
}
