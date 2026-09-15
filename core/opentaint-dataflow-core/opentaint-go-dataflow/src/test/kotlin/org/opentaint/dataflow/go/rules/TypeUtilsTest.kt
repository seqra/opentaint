package org.opentaint.dataflow.go.rules

import org.opentaint.ir.go.type.GoIRNamedTypeRef
import org.opentaint.ir.go.type.GoIRPointerType
import org.opentaint.ir.go.type.NamedTypeRef
import kotlin.test.Test
import kotlin.test.assertEquals
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

    @Test
    fun `split package function name`() {
        assertEquals("strings" to "Clone", "strings.Clone".splitFullName())
        assertEquals("github.com/acme/pkg" to "Clone", "github.com/acme/pkg.Clone".splitFullName())
        assertEquals("" to "make", "make".splitFullName())
    }

    @Test
    fun `split generic function with qualified type arguments`() {
        val name = "test/util.GenericIdentity[test/model.NamedString]"
        assertEquals("test/util" to "GenericIdentity[test/model.NamedString]", name.splitFullName())
    }

    @Test
    fun `split generic function with nested qualified type arguments`() {
        val name = "test/util.Clone[[]test/model.Box[test/inner.Value] test/model.Box[test/inner.Value]]"
        val function = "Clone[[]test/model.Box[test/inner.Value] test/model.Box[test/inner.Value]]"
        assertEquals("test/util" to function, name.splitFullName())
    }

    @Test
    fun `split method on generic receiver`() {
        val name = "(*test/util.Box[test/model.Value]).Get"
        assertEquals("(*test/util.Box[test/model.Value])" to "Get", name.splitFullName())
    }
}
