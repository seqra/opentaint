package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.go.pattern.conversion.GoConcreteType
import org.opentaint.semgrep.go.pattern.conversion.GoTypeOps
import org.opentaint.semgrep.go.pattern.conversion.goNamed
import org.opentaint.semgrep.go.pattern.conversion.goQualified
import org.opentaint.semgrep.pattern.ResolvedMetaVarInfo
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull

class GoTypeOpsTest {
    private val noInfo = ResolvedMetaVarInfo(emptySet(), emptyMap())
    private fun unify(a: TypeConstraint, b: TypeConstraint) = unifyTypeConstraint(a, b, noInfo, GoTypeOps)
    @Test fun sameQualifiedUnifies() = assertEquals(goQualified("net/http", "Cookie"), unify(goQualified("net/http", "Cookie"), goQualified("net/http", "Cookie")))
    @Test fun differentNamedFails() = assertNull(unify(goNamed("A"), goNamed("B")))
    @Test fun pointerUnifiesElementwise() {
        val p = TypeConstraint.Concrete(GoConcreteType.Pointer(goNamed("T")))
        assertEquals(p, unify(p, p))
    }
    @Test fun anyAbsorbs() = assertEquals(goNamed("T"), unify(TypeConstraint.Any, goNamed("T")))
}
