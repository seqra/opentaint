package org.opentaint.ir.impl.python.transforms.closure

import org.opentaint.ir.impl.python.flat.FlatInst

internal class InstRewriterScope(original: FlatInst) {
    private val pre = ArrayList<FlatInst>()
    private var core: FlatInst = original
    private val post = ArrayList<FlatInst>()

    fun emitBefore(inst: FlatInst) { pre += inst }
    fun emitAfter(inst: FlatInst) { post += inst }

    fun replaceWith(inst: FlatInst) { core = inst }

    fun finish(): List<FlatInst> = pre + core + post
}
