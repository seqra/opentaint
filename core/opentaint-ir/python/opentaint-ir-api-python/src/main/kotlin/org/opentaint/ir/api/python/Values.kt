package org.opentaint.ir.api.python

import org.opentaint.ir.api.common.cfg.CommonValue

sealed interface PIRValue : PIRExpr, CommonValue {
    val type: PIRType
    override val typeName: String get() = type.typeName
    fun <T> accept(visitor: PIRValueVisitor<T>): T
}

sealed interface PIRLocal : PIRValue {
    val name: String
    val index: Int
}

class PIRLocalVar(
    override val name: String,
    override val type: PIRType,
    override val index: Int,
) : PIRLocal {
    override fun toString(): String = "%$index"
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitLocalVar(this)

    override fun equals(other: Any?): Boolean =
        this === other || (other is PIRLocalVar && other.index == index)
    override fun hashCode(): Int = index
}

class PIRParameterRef(
    override val name: String,
    override val type: PIRType,
    override val index: Int,
) : PIRLocal {
    override fun toString(): String = "%$index"
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitParameterRef(this)

    override fun equals(other: Any?): Boolean =
        this === other || (other is PIRParameterRef && other.index == index)
    override fun hashCode(): Int = index
}

sealed interface PIRConst : PIRValue

data class PIRIntConst(val value: Long) : PIRConst {
    override val type: PIRType get() = PIRClassType("builtins.int")
    override fun toString(): String = value.toString()
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitIntConst(this)
}

data class PIRFloatConst(val value: Double) : PIRConst {
    override val type: PIRType get() = PIRClassType("builtins.float")
    override fun toString(): String = value.toString()
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitFloatConst(this)
}

data class PIRStrConst(val value: String) : PIRConst {
    override val type: PIRType get() = PIRClassType("builtins.str")
    override fun toString(): String = "\"$value\""
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitStrConst(this)
}

data class PIRBoolConst(val value: Boolean) : PIRConst {
    override val type: PIRType get() = PIRClassType("builtins.bool")
    override fun toString(): String = if (value) "True" else "False"
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitBoolConst(this)
}

data object PIRNoneConst : PIRConst {
    override val type: PIRType = PIRNoneType
    override fun toString(): String = "None"
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitNoneConst(this)
}

data object PIREllipsisConst : PIRConst {
    override val type: PIRType = PIRAnyType
    override fun toString(): String = "..."
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitEllipsisConst(this)
}

data class PIRBytesConst(val value: ByteArray) : PIRConst {
    override val type: PIRType get() = PIRClassType("builtins.bytes")
    override fun equals(other: Any?): Boolean =
        other is PIRBytesConst && value.contentEquals(other.value)
    override fun hashCode(): Int = value.contentHashCode()
    override fun toString(): String = "b\"...\""
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitBytesConst(this)
}

data class PIRComplexConst(val real: Double, val imag: Double) : PIRConst {
    override val type: PIRType get() = PIRClassType("builtins.complex")
    override fun toString(): String = "${real}+${imag}j"
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitComplexConst(this)
}

sealed interface PIRNameRef

data class PIRGlobalNameRef(val qualifiedName: String) : PIRNameRef {
    override fun toString(): String = qualifiedName
}

data class PIRModuleNameRef(val module: String) : PIRNameRef {
    init {
        require('.' !in module) { "PIRModuleNameRef.module must be a single segment, got '$module'" }
    }
    override fun toString(): String = module
}
