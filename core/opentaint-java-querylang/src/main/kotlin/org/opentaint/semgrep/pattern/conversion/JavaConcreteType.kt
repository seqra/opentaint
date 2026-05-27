package org.opentaint.semgrep.pattern.conversion

import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import org.opentaint.semgrep.pattern.MetaVarConstraints
import org.opentaint.semgrep.pattern.ResolvedMetaVarInfo
import org.opentaint.semgrep.pattern.conversion.taint.stringMatches

@Serializable
sealed interface JavaConcreteType : LanguageConcreteType {
    @Serializable @SerialName("java.fq")
    data class FullyQualified(val name: String, val typeArgs: List<TypeConstraint> = emptyList()) : JavaConcreteType {
        override fun toString(): String = if (typeArgs.isEmpty()) name else "$name<${typeArgs.joinToString(", ")}>"
    }

    @Serializable @SerialName("java.cls")
    data class ClassName(val name: String, val typeArgs: List<TypeConstraint> = emptyList()) : JavaConcreteType {
        override fun toString(): String = if (typeArgs.isEmpty()) "*.$name" else "*.$name<${typeArgs.joinToString(", ")}>"
    }

    @Serializable @SerialName("java.prim")
    data class PrimitiveName(val name: String) : JavaConcreteType {
        override fun toString(): String = name
    }

    @Serializable @SerialName("java.arr")
    data class ArrayType(val element: TypeConstraint) : JavaConcreteType {
        override fun toString(): String = "$element[]"
    }
}

fun javaFq(name: String, typeArgs: List<TypeConstraint> = emptyList()): TypeConstraint =
    TypeConstraint.Concrete(JavaConcreteType.FullyQualified(name, typeArgs))

fun javaClass(name: String, typeArgs: List<TypeConstraint> = emptyList()): TypeConstraint =
    TypeConstraint.Concrete(JavaConcreteType.ClassName(name, typeArgs))

fun javaPrimitive(name: String): TypeConstraint =
    TypeConstraint.Concrete(JavaConcreteType.PrimitiveName(name))

fun javaArray(element: TypeConstraint): TypeConstraint =
    TypeConstraint.Concrete(JavaConcreteType.ArrayType(element))

object JavaTypeOps : LanguageTypeOps {
    override fun unifyConcrete(
        left: LanguageConcreteType,
        right: LanguageConcreteType,
        metaVarInfo: ResolvedMetaVarInfo,
    ): TypeConstraint? {
        left as JavaConcreteType
        right as JavaConcreteType
        // identical concretes are already handled by unifyTypeConstraint's `left == right` fast path
        return when (left) {
            is JavaConcreteType.PrimitiveName -> null
            is JavaConcreteType.ClassName -> when (right) {
                is JavaConcreteType.ArrayType, is JavaConcreteType.PrimitiveName -> null
                is JavaConcreteType.ClassName -> {
                    if (left.name != right.name) null
                    else unifyTypeArgs(left.typeArgs, right.typeArgs, metaVarInfo)?.let { javaClass(left.name, it) }
                }
                is JavaConcreteType.FullyQualified ->
                    if (right.name.endsWith(left.name))
                        unifyTypeArgs(left.typeArgs, right.typeArgs, metaVarInfo)?.let { javaFq(right.name, it) }
                    else null
            }
            is JavaConcreteType.FullyQualified -> when (right) {
                is JavaConcreteType.ArrayType, is JavaConcreteType.PrimitiveName -> null
                is JavaConcreteType.ClassName ->
                    if (left.name.endsWith(right.name))
                        unifyTypeArgs(left.typeArgs, right.typeArgs, metaVarInfo)?.let { javaFq(left.name, it) }
                    else null
                is JavaConcreteType.FullyQualified ->
                    if (left.name != right.name) null
                    else unifyTypeArgs(left.typeArgs, right.typeArgs, metaVarInfo)?.let { javaFq(left.name, it) }
            }
            is JavaConcreteType.ArrayType -> when (right) {
                is JavaConcreteType.ArrayType ->
                    unifyTypeConstraint(left.element, right.element, metaVarInfo, this)?.let { javaArray(it) }
                else -> null
            }
        }
    }

    private fun unifyTypeArgs(
        left: List<TypeConstraint>,
        right: List<TypeConstraint>,
        metaVarInfo: ResolvedMetaVarInfo,
    ): List<TypeConstraint>? {
        if (left.isEmpty()) return right
        if (right.isEmpty()) return left
        if (left.size != right.size) return null
        return left.zip(right).map { (l, r) -> unifyTypeConstraint(l, r, metaVarInfo, this) ?: return null }
    }

    override fun metavarsOf(type: LanguageConcreteType): Set<String> {
        type as JavaConcreteType
        return when (type) {
            is JavaConcreteType.PrimitiveName -> emptySet()
            is JavaConcreteType.ArrayType -> type.element.collectMetavars(this)
            is JavaConcreteType.ClassName -> type.typeArgs.flatMapTo(mutableSetOf()) { it.collectMetavars(this) }
            is JavaConcreteType.FullyQualified -> type.typeArgs.flatMapTo(mutableSetOf()) { it.collectMetavars(this) }
        }
    }

    override fun concreteMatchesMetaVarConstraint(type: LanguageConcreteType, constraints: MetaVarConstraints?): Boolean {
        type as JavaConcreteType
        return when (type) {
            is JavaConcreteType.ClassName -> stringMatches(type.name, constraints)
            is JavaConcreteType.FullyQualified -> type.name != generatedMethodClassName && stringMatches(type.name, constraints)
            is JavaConcreteType.PrimitiveName, is JavaConcreteType.ArrayType -> false
        }
    }
}
