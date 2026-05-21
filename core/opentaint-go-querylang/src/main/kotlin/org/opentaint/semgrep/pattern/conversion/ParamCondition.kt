package org.opentaint.semgrep.pattern.conversion

sealed interface TypePattern {
    data class Named(val name: String) : TypePattern
    data class Qualified(val pkg: String, val name: String) : TypePattern
    data class Pointer(val elem: TypePattern) : TypePattern
    data class Slice(val elem: TypePattern) : TypePattern
    data class Map(val key: TypePattern, val value: TypePattern) : TypePattern
    data class MetaVar(val metaVar: String) : TypePattern
    data object Any : TypePattern
}

sealed interface ParamPosition {
    data class Concrete(val idx: Int) : ParamPosition
    data class Any(val classifier: String) : ParamPosition
    data class Named(val field: String) : ParamPosition
}

sealed interface ParamCondition {
    data class And(val conditions: List<ParamCondition>) : ParamCondition
    data object True : ParamCondition

    sealed interface Atom : ParamCondition
    data class TypeIs(val typeName: TypePattern) : Atom
    data object AnyStringLiteral : Atom
    data class StringValueMetaVar(val metaVar: MetavarAtom) : Atom
    data class IsMetavar(val metavar: MetavarAtom) : Atom
    data class SpecificBoolValue(val value: Boolean) : Atom
    data class SpecificIntValue(val value: String) : Atom
    data class SpecificStringValue(val value: String) : Atom
    data object SpecificNilValue : Atom
}

sealed interface MetavarAtom {
    data class Basic(val name: String) : MetavarAtom {
        val isArtificial: Boolean get() = name.startsWith(ARTIFICIAL_PREFIX)
    }

    companion object {
        private const val ARTIFICIAL_PREFIX = "\$<ARTIFICIAL>"
        fun create(name: String): MetavarAtom = Basic(name)
        fun createArtificial(classifier: String): MetavarAtom = Basic("${ARTIFICIAL_PREFIX}_$classifier")
    }
}

data class ParamPattern(val position: ParamPosition, val condition: ParamCondition)

sealed interface ParamConstraint {
    val conditions: List<ParamCondition>

    data class Concrete(val params: List<ParamCondition>) : ParamConstraint {
        override val conditions: List<ParamCondition> get() = params
    }

    data class Partial(val params: List<ParamPattern>) : ParamConstraint {
        override val conditions: List<ParamCondition> get() = params.map { it.condition }
    }
}

fun mkAnd(conditions: List<ParamCondition>): ParamCondition = when (conditions.size) {
    0 -> ParamCondition.True
    1 -> conditions.first()
    else -> ParamCondition.And(conditions)
}
