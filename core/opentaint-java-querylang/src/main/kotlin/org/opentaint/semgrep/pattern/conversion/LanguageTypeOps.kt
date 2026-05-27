package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.MetaVarConstraints
import org.opentaint.semgrep.pattern.ResolvedMetaVarInfo

/** Per-language operations on concrete type payloads, used by the shared simplifier/automata. */
interface LanguageTypeOps {
    /**
     * Unify two concrete payloads; null = no match.
     * Implementations recurse into nested type constraints by calling [unifyTypeConstraint] and passing
     * themselves as the `typeOps` argument.
     */
    fun unifyConcrete(left: LanguageConcreteType, right: LanguageConcreteType, metaVarInfo: ResolvedMetaVarInfo): TypeConstraint?

    /** All metavars referenced inside the concrete payload (recursively through nested type constraints). */
    fun metavarsOf(type: LanguageConcreteType): Set<String>

    /** Does this concrete payload satisfy a metavar's string constraint? (metavar-vs-concrete unification.) */
    fun concreteMatchesMetaVarConstraint(type: LanguageConcreteType, constraints: MetaVarConstraints?): Boolean
}
