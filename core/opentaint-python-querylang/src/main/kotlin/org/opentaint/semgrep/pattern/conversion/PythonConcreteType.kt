package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.MetaVarConstraints
import org.opentaint.semgrep.pattern.ResolvedMetaVarInfo

/** Python concrete type — only a (possibly dotted) name; v1 has no nested/generic types. */
sealed interface PythonConcreteType : LanguageConcreteType {
    /** [name] may be a dotted path, e.g. `flask.views.View`. */
    data class Named(val name: String) : PythonConcreteType { override fun toString() = name }
}

fun pythonNamed(name: String) = TypeConstraint.Concrete(PythonConcreteType.Named(name))

/**
 * Degenerate type operations: Python has a single [PythonConcreteType.Named] payload with no
 * nested element types, so unification reduces to name equality (already handled by
 * [unifyTypeConstraint]'s `left == right` fast path) and there are no constraints to check.
 * Mirrors `GoTypeOps`' `Named` branch.
 */
object PythonTypeOps : LanguageTypeOps {
    override fun unifyConcrete(
        left: LanguageConcreteType,
        right: LanguageConcreteType,
        metaVarInfo: ResolvedMetaVarInfo,
    ): TypeConstraint? = null  // non-equal Named never unifies; equality handled upstream

    override fun metavarsOf(type: LanguageConcreteType): Set<String> = emptySet()

    override fun concreteMatchesMetaVarConstraint(
        type: LanguageConcreteType,
        constraints: MetaVarConstraints?,
    ): Boolean = constraints == null
}
