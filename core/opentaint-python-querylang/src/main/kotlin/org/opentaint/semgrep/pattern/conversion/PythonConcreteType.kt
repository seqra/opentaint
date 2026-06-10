package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.MetaVarConstraints
import org.opentaint.semgrep.pattern.ResolvedMetaVarInfo

/** TODO: Python concrete type representation for metavar/type constraints. */
sealed interface PythonConcreteType : LanguageConcreteType {
    data class Named(val name: String) : PythonConcreteType
}

/** TODO: type unification / constraint matching for Python. */
object PythonTypeOps : LanguageTypeOps {
    override fun unifyConcrete(
        left: LanguageConcreteType,
        right: LanguageConcreteType,
        metaVarInfo: ResolvedMetaVarInfo,
    ): TypeConstraint? = TODO("Python type unification not implemented")

    override fun metavarsOf(type: LanguageConcreteType): Set<String> =
        TODO("Python metavarsOf not implemented")

    override fun concreteMatchesMetaVarConstraint(
        type: LanguageConcreteType,
        constraints: MetaVarConstraints?,
    ): Boolean = TODO("Python concreteMatchesMetaVarConstraint not implemented")
}
