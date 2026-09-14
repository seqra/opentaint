package org.opentaint.ir.approximations.target

interface InterfaceTarget {
    fun convert(value: String): String
}

class InterfaceTargetImplementation : InterfaceTarget {
    override fun convert(value: String): String = "opaque"
}
