package org.opentaint.dataflow.go.rules

import org.opentaint.ir.go.type.GoIRNamedTypeRef
import org.opentaint.ir.go.type.GoIRPointerType
import org.opentaint.ir.go.type.NamedTypeRef
import kotlin.test.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class TypeUtilsTest {
    private fun named(pkg: String, name: String) = GoIRNamedTypeRef(NamedTypeRef(pkg, name), emptyList())
    private fun ptr(pkg: String, name: String) = GoIRPointerType(named(pkg, name))

    @Test
    fun `import-qualified pointer receiver matches the full import path exactly`() {
        assertTrue(matchesType(ptr("os/exec", "Cmd"), "*os/exec.Cmd"))
    }

    @Test
    fun `bare selector still tail-matches the full import path`() {
        assertTrue(matchesType(ptr("os/exec", "Cmd"), "*exec.Cmd"))
        assertTrue(matchesType(ptr("database/sql", "DB"), "*sql.DB"))
    }

    @Test
    fun `slash-qualified package does not tail-match a shorter package`() {
        assertFalse(matchesType(ptr("exec", "Cmd"), "*os/exec.Cmd"))
    }

    @Test
    fun `different fully-qualified package does not match`() {
        assertFalse(matchesType(ptr("other/exec", "Cmd"), "*os/exec.Cmd"))
    }

    @Test
    fun `mismatched simple name does not match`() {
        assertFalse(matchesType(ptr("os/exec", "Cmd"), "*os/exec.Other"))
    }
}
