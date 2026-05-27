package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.MetaVarConstraintFormula
import org.opentaint.semgrep.pattern.MetaVarConstraints
import org.opentaint.semgrep.pattern.MetaVarConstraint
import org.opentaint.semgrep.pattern.ResolvedMetaVarInfo
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull

class TypeConstraintOpsTest {
    private val noInfo = ResolvedMetaVarInfo(emptySet(), emptyMap())

    // Minimal fake concrete type so the shared ops can be tested without a language module.
    private data class FakeConcrete(val n: String) : LanguageConcreteType

    private val ops = object : LanguageTypeOps {
        override fun unifyConcrete(left: LanguageConcreteType, right: LanguageConcreteType, metaVarInfo: ResolvedMetaVarInfo) =
            if (left == right) TypeConstraint.Concrete(left) else null
        override fun metavarsOf(type: LanguageConcreteType) = emptySet<String>()
        override fun concreteMatchesMetaVarConstraint(type: LanguageConcreteType, constraints: MetaVarConstraints?) = constraints == null
    }

    @Test fun anyAbsorbs() {
        val c = TypeConstraint.Concrete(FakeConcrete("x"))
        assertEquals(c, unifyTypeConstraint(TypeConstraint.Any, c, noInfo, ops))
        assertEquals(c, unifyTypeConstraint(c, TypeConstraint.Any, noInfo, ops))
    }

    @Test fun metavarVsConcreteUsesOps() {
        val c = TypeConstraint.Concrete(FakeConcrete("x"))
        assertEquals(c, unifyTypeConstraint(TypeConstraint.MetaVar("\$T"), c, noInfo, ops))
    }

    @Test fun concreteMismatchFails() {
        val a = TypeConstraint.Concrete(FakeConcrete("a"))
        val b = TypeConstraint.Concrete(FakeConcrete("b"))
        assertNull(unifyTypeConstraint(a, b, noInfo, ops))
    }

    @Test fun collectMetavarsOfMetaVar() {
        assertEquals(setOf("\$T"), TypeConstraint.MetaVar("\$T").collectMetavars(ops))
    }

    @Test fun metavarWithFailingConstraintFails() {
        val constraints = MetaVarConstraints(MetaVarConstraintFormula.Constraint(MetaVarConstraint.RegExp("x")))
        val info = ResolvedMetaVarInfo(emptySet(), mapOf("\$T" to constraints))
        val c = TypeConstraint.Concrete(FakeConcrete("x"))
        // fake ops returns false when constraints != null -> unification fails
        assertNull(unifyTypeConstraint(TypeConstraint.MetaVar("\$T"), c, info, ops))
    }
}
