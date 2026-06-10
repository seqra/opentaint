package org.opentaint.semgrep.go.pattern.conversion

import org.opentaint.semgrep.pattern.MetaVarConstraints
import org.opentaint.semgrep.pattern.ResolvedMetaVarInfo
import org.opentaint.semgrep.pattern.conversion.LanguageConcreteType
import org.opentaint.semgrep.pattern.conversion.LanguageTypeOps
import org.opentaint.semgrep.pattern.conversion.TypeConstraint
import org.opentaint.semgrep.pattern.conversion.collectMetavars
import org.opentaint.semgrep.pattern.conversion.unifyTypeConstraint

sealed interface GoConcreteType : LanguageConcreteType {
    data class Named(val name: String) : GoConcreteType { override fun toString() = name }
    data class Qualified(val pkg: String, val name: String) : GoConcreteType { override fun toString() = "$pkg.$name" }
    data class Pointer(val elem: TypeConstraint) : GoConcreteType { override fun toString() = "*$elem" }
    data class Slice(val elem: TypeConstraint) : GoConcreteType { override fun toString() = "[]$elem" }
    data class MapType(val key: TypeConstraint, val value: TypeConstraint) : GoConcreteType {
        override fun toString() = "map[$key]$value"
    }
}

fun goNamed(name: String): TypeConstraint = TypeConstraint.Concrete(GoConcreteType.Named(name))
fun goQualified(pkg: String, name: String): TypeConstraint = TypeConstraint.Concrete(GoConcreteType.Qualified(pkg, name))

object GoTypeOps : LanguageTypeOps {
    override fun unifyConcrete(left: LanguageConcreteType, right: LanguageConcreteType, metaVarInfo: ResolvedMetaVarInfo): TypeConstraint? {
        left as GoConcreteType
        right as GoConcreteType
        return when (left) {
            is GoConcreteType.Named, is GoConcreteType.Qualified -> null  // non-equal handled by unifyTypeConstraint fast path
            is GoConcreteType.Pointer -> (right as? GoConcreteType.Pointer)?.let {
                unifyTypeConstraint(left.elem, it.elem, metaVarInfo, this)?.let { e -> TypeConstraint.Concrete(GoConcreteType.Pointer(e)) }
            }
            is GoConcreteType.Slice -> (right as? GoConcreteType.Slice)?.let {
                unifyTypeConstraint(left.elem, it.elem, metaVarInfo, this)?.let { e -> TypeConstraint.Concrete(GoConcreteType.Slice(e)) }
            }
            is GoConcreteType.MapType -> (right as? GoConcreteType.MapType)?.let {
                val k = unifyTypeConstraint(left.key, it.key, metaVarInfo, this) ?: return null
                val v = unifyTypeConstraint(left.value, it.value, metaVarInfo, this) ?: return null
                TypeConstraint.Concrete(GoConcreteType.MapType(k, v))
            }
        }
    }
    override fun metavarsOf(type: LanguageConcreteType): Set<String> {
        type as GoConcreteType
        return when (type) {
            is GoConcreteType.Named, is GoConcreteType.Qualified -> emptySet()
            is GoConcreteType.Pointer -> type.elem.collectMetavars(this)
            is GoConcreteType.Slice -> type.elem.collectMetavars(this)
            is GoConcreteType.MapType -> type.key.collectMetavars(this) + type.value.collectMetavars(this)
        }
    }
    override fun concreteMatchesMetaVarConstraint(type: LanguageConcreteType, constraints: MetaVarConstraints?): Boolean =
        constraints == null
}
