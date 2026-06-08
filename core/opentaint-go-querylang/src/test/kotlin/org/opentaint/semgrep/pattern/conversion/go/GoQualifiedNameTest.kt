package org.opentaint.semgrep.pattern.conversion.go

import org.opentaint.semgrep.go.pattern.conversion.GoConcreteType
import org.opentaint.semgrep.go.pattern.conversion.go.goQualifiedName
import org.opentaint.semgrep.go.pattern.conversion.goNamed
import org.opentaint.semgrep.go.pattern.conversion.goQualified
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.SignatureName
import org.opentaint.semgrep.pattern.conversion.TypeConstraint
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull

class GoQualifiedNameTest {
    @Test fun packageQualifiedFunction() =
        assertEquals("net/http.Get", goQualifiedName(SignatureName.Concrete("Get"), goQualified("net/http", "Get")))

    @Test fun packageSelectorNamed() =
        assertEquals("util.Source", goQualifiedName(SignatureName.Concrete("Source"), goNamed("util")))

    @Test fun valueReceiverMethod() =
        assertEquals("DB.Query", goQualifiedName(SignatureName.Concrete("Query"), goNamed("DB")))

    @Test fun pointerReceiverMethod() =
        assertEquals("(*DB).Query",
            goQualifiedName(SignatureName.Concrete("Query"),
                TypeConstraint.Concrete(GoConcreteType.Pointer(goNamed("DB")))))

    @Test fun noEnclosingIsBareName() =
        assertEquals("Source", goQualifiedName(SignatureName.Concrete("Source"), null))

    @Test fun anyEnclosingIsBareName() =
        assertEquals("Source", goQualifiedName(SignatureName.Concrete("Source"), TypeConstraint.Any))

    @Test fun metavarMethodNameIsNull() =
        assertNull(goQualifiedName(SignatureName.MetaVar("\$F"), null))

    @Test fun anyMethodNameIsNull() =
        assertNull(goQualifiedName(SignatureName.AnyName, null))

    @Test fun metavarEnclosingIsNull() =
        assertNull(goQualifiedName(SignatureName.Concrete("Query"), TypeConstraint.MetaVar("\$T")))
}
