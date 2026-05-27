package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.ResolvedMetaVarInfo
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull

class JavaTypeOpsTest {
    private val noInfo = ResolvedMetaVarInfo(emptySet(), emptyMap())
    private fun unify(a: TypeConstraint, b: TypeConstraint) = unifyTypeConstraint(a, b, noInfo, JavaTypeOps)

    @Test fun classNameMatchesFqBySuffix() {
        assertEquals(javaFq("java.lang.String"), unify(javaClass("String"), javaFq("java.lang.String")))
    }
    @Test fun primitiveOnlyEqual() {
        assertEquals(javaPrimitive("int"), unify(javaPrimitive("int"), javaPrimitive("int")))
        assertNull(unify(javaPrimitive("int"), javaPrimitive("long")))
    }
    @Test fun arrayUnifiesElementwise() {
        assertEquals(javaArray(javaFq("java.lang.String")),
            unify(javaArray(javaClass("String")), javaArray(javaFq("java.lang.String"))))
    }
    @Test fun mismatchedKindsFail() {
        assertNull(unify(javaPrimitive("int"), javaClass("String")))
    }

    @Test fun fullyQualifiedNameMismatchFails() {
        assertNull(unify(javaFq("java.util.List"), javaFq("java.lang.String")))
    }

    @Test fun typeArgsUnifyThrough() {
        assertEquals(
            javaFq("java.util.List", listOf(javaFq("java.lang.String"))),
            unify(javaFq("java.util.List", listOf(javaClass("String"))),
                  javaFq("java.util.List", listOf(javaFq("java.lang.String"))))
        )
    }
}
