package org.opentaint.ir.go.value

interface GoIRValueVisitor<out T> {
    fun visitConst(value: GoIRConstValue): T
    fun visitParameter(value: GoIRParameterValue): T
    fun visitFreeVar(value: GoIRFreeVarValue): T
    fun visitRegister(value: GoIRRegister): T

    interface Default<out T> : GoIRValueVisitor<T> {
        fun defaultVisitValue(value: GoIRValue): T

        override fun visitConst(value: GoIRConstValue) = defaultVisitValue(value)
        override fun visitParameter(value: GoIRParameterValue) = defaultVisitValue(value)
        override fun visitFreeVar(value: GoIRFreeVarValue) = defaultVisitValue(value)
        override fun visitRegister(value: GoIRRegister) = defaultVisitValue(value)
    }
}
