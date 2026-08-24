package org.opentaint.ir.impl.python.protoToFlat

internal class Scope {
    private var tempCounter = 0

    fun newTemp(): String = "\$t${tempCounter++}"

    fun resolveLocal(name: String): String = name
}
