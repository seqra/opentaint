package org.opentaint.dataflow.jvm.ap.ifds

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAccessor
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class JIRAliasAccessorTypeValidationTest {
    @Test
    fun `rejects field access when receiver types cannot overlap`() {
        val previous = field("java.io.File", "path", "java.lang.String")
        val next = field("org.example.Settings", "tenantId", "org.example.TenantId")

        val valid = isValidAliasAccessorTransition(previous, next) { actual, required ->
            assertTrue(actual == "java.lang.String")
            assertTrue(required == "org.example.Settings")
            false
        }

        assertFalse(valid)
    }

    @Test
    fun `accepts field access when receiver and field owner may overlap`() {
        val previous = field("org.example.Container", "value", "org.example.HasTenant")
        val next = field("org.example.Settings", "tenantId", "org.example.TenantId")

        assertTrue(isValidAliasAccessorTransition(previous, next) { _, _ -> true })
    }

    @Test
    fun `accepts field owner connected to receiver through a common subtype`() {
        val previous = field("org.example.Container", "a", "org.example.A")
        val next = field("org.example.X", "value", "java.lang.Object")

        assertTrue(isValidAliasAccessorTransition(previous, next) { receiver, owner ->
            assertTrue(receiver == "org.example.A")
            assertTrue(owner == "org.example.X")
            // Y extends X and implements A, although X itself is not assignable to A.
            true
        })
    }

    @Test
    fun `validates a field following a static base`() {
        val previous = AliasAccessor.Static("org.example.Settings")
        val next = field("org.example.Settings", "DEFAULT", "org.example.Settings")

        assertTrue(isValidAliasAccessorTransition(previous, next) { actual, required ->
            actual == required
        })
    }

    @Test
    fun `keeps transitions without enough type information`() {
        val field = field("org.example.Settings", "tenantId", "org.example.TenantId")
        val rejectAll: (String, String) -> Boolean = { _, _ -> false }

        assertTrue(isValidAliasAccessorTransition(null, field, rejectAll))
    }

    @Test
    fun `rejects access after an unbounded accessor`() {
        assertFalse {
            isValidAliasAccessorTransition(
                AliasAccessor.Array,
                field("test.Node", "next", "test.Node"),
                { _, _ -> true },
            )
        }
        assertFalse {
            isValidAliasAccessorTransition(
                field("java.lang.Iterable", "Element", "java.lang.Object"),
                field("test.Node", "next", "test.Node"),
                { _, _ -> true },
            )
        }
    }

    @Test
    fun `rejects erased accessor after another accessor`() {
        assertFalse {
            isValidAliasAccessorTransition(
                field("test.Container", "values", "java.util.Map"),
                field("org.apache.commons.collections4.Get", "MapValue", "java.lang.Object"),
                { _, _ -> true },
            )
        }
    }

    @Test
    fun `accepts array accessor after typed array field`() {
        assertTrue {
            isValidAliasAccessorTransition(
                field("test.Container", "values", "java.lang.Object[]"),
                AliasAccessor.Array,
                { _, _ -> false },
            )
        }
    }

    @Test
    fun `rejects first field incompatible with alias base`() {
        val first = field("java.util.Optional", "Element", "java.lang.Object")

        val valid = isValidAliasBaseAccessorTransition("org.example.HasName", first) { actual, required ->
            assertTrue(actual == "org.example.HasName")
            assertTrue(required == "java.util.Optional")
            false
        }

        assertFalse(valid)
    }

    @Test
    fun `keeps first field when base type is unknown`() {
        val first = field("java.util.Optional", "Element", "java.lang.Object")

        assertTrue(isValidAliasBaseAccessorTransition(null, first) { _, _ -> false })
    }

    @Test
    fun `accepts first field when base and owner have a common subtype`() {
        val first = field("org.example.X", "value", "java.lang.Object")

        assertTrue(isValidAliasBaseAccessorTransition("org.example.A", first) { base, owner ->
            base == "org.example.A" && owner == "org.example.X"
        })
    }

    @Test
    fun `rejects an alias whose result type cannot match the query type`() {
        assertFalse(isAliasResultTypeCompatible("org.example.HasName", "java.lang.String") { _, _ -> false })
    }

    @Test
    fun `accepts an alias whose result type may match the query type`() {
        assertTrue(isAliasResultTypeCompatible("org.example.HasName", "org.example.Customer") { _, _ -> true })
    }

    @Test
    fun `does not infer a result type for a direct alias`() {
        val alias = AliasApInfo(AccessPathBase.LocalVar(1), emptyList())

        assertEquals(null, alias.heapResultTypeName())
    }

    @Test
    fun `uses the last heap field type as the alias result type`() {
        val alias = AliasApInfo(
            AccessPathBase.LocalVar(1),
            listOf(field("test.Container", "value", "test.Value")),
        )

        assertEquals("test.Value", alias.heapResultTypeName())
    }

    private fun field(className: String, fieldName: String, fieldType: String) =
        AliasAccessor.Field(className, fieldName, fieldType)
}
