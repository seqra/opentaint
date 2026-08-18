package org.opentaint.dataflow.jvm.ap.ifds

import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAccessor
import kotlin.test.Test
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
    fun `accepts field access when receiver types may overlap`() {
        val previous = field("org.example.Container", "value", "org.example.HasTenant")
        val next = field("org.example.Settings", "tenantId", "org.example.TenantId")

        assertTrue(isValidAliasAccessorTransition(previous, next) { _, _ -> true })
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
        assertTrue(isValidAliasAccessorTransition(AliasAccessor.Array, field, rejectAll))
        assertTrue(isValidAliasAccessorTransition(field, AliasAccessor.Array, rejectAll))
    }

    private fun field(className: String, fieldName: String, fieldType: String) =
        AliasAccessor.Field(className, fieldName, fieldType)
}
