package org.opentaint.semgrep.pattern.conversion

import kotlinx.serialization.Serializable
import org.opentaint.semgrep.pattern.ResolvedMetaVarInfo

/** Language-neutral type constraint: any value, a metavar, or a language-specific concrete type. */
@Serializable
sealed interface TypeConstraint {
    @Serializable
    data object Any : TypeConstraint {
        override fun toString(): String = "*"
    }

    @Serializable
    data class MetaVar(val metaVar: String) : TypeConstraint {
        override fun toString(): String = metaVar
    }

    @Serializable
    data class Concrete(val type: LanguageConcreteType) : TypeConstraint {
        override fun toString(): String = type.toString()
    }
}

/**
 * Marker for a language-specific concrete type payload (Java FQN/class/primitive/array, Go named/qualified/pointer/...).
 * Implementations must be value types (structural equals/hashCode) and serializable.
 * Polymorphic serialization; runtime use (only the benchmark today) requires a SerializersModule
 * registering the concrete subclasses. Live paths do not serialize it.
 */
interface LanguageConcreteType

/** Shared unification: Any/MetaVar handled here; Concrete-vs-Concrete delegated to [typeOps]. */
fun unifyTypeConstraint(
    left: TypeConstraint,
    right: TypeConstraint,
    metaVarInfo: ResolvedMetaVarInfo,
    typeOps: LanguageTypeOps,
): TypeConstraint? {
    if (left == right) return left
    return when (left) {
        TypeConstraint.Any -> right
        is TypeConstraint.MetaVar -> when (right) {
            TypeConstraint.Any -> left
            is TypeConstraint.MetaVar -> {
                // Faithful port of the original unifyTypeName: an unconstrained metavar acts as a
                // wildcard and unifies to the other (more-constrained) side. Two constrained metavars
                // would need constraint intersection, which is not yet implemented.
                metaVarInfo.metaVarConstraints[left.metaVar] ?: return right
                metaVarInfo.metaVarConstraints[right.metaVar] ?: return left
                TODO("Type metavar constraints intersection")
            }
            is TypeConstraint.Concrete ->
                if (typeOps.concreteMatchesMetaVarConstraint(right.type, metaVarInfo.metaVarConstraints[left.metaVar])) right else null
        }
        is TypeConstraint.Concrete -> when (right) {
            TypeConstraint.Any -> left
            is TypeConstraint.MetaVar ->
                if (typeOps.concreteMatchesMetaVarConstraint(left.type, metaVarInfo.metaVarConstraints[right.metaVar])) left else null
            is TypeConstraint.Concrete -> typeOps.unifyConcrete(left.type, right.type, metaVarInfo)
        }
    }
}

/** Shared metavar collection: Any -> none, MetaVar -> itself, Concrete -> delegated to [typeOps]. */
fun TypeConstraint.collectMetavars(typeOps: LanguageTypeOps): Set<String> = when (this) {
    TypeConstraint.Any -> emptySet()
    is TypeConstraint.MetaVar -> setOf(metaVar)
    is TypeConstraint.Concrete -> typeOps.metavarsOf(type)
}
