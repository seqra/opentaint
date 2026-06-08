package org.opentaint.dataflow.go.analysis.alias

import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class GoAliasFactsTest {
    @Test
    fun `infoKind ordering matches jvm`() {
        val alloc = GoLocalAlias.Alloc(inst = 7, ctx = ContextInfo.rootContext)
        val ret = GoReturnValue(callInst = 7, ctx = ContextInfo.rootContext)
        val simple = GoLocalAlias.SimpleLoc(GoRefValue.Arg(0))
        val unknown = GoUnknown(inst = 7, ctx = ContextInfo.rootContext)
        assertEquals(0, alloc.infoKind)
        assertEquals(1, ret.infoKind)
        assertEquals(2, simple.infoKind)
        assertEquals(3, unknown.infoKind)
    }

    @Test
    fun `accessor kinds are distinct`() {
        val field = GoFieldAlias(GoAliasAccessor.Field("C", "f"))
        assertEquals(0, field.accessorKind)
        assertEquals(1, GoArrayAlias.accessorKind)
        assertEquals(2, GoRefAlias.accessorKind)
    }

    @Test
    fun `simple loc compares by ref value`() {
        val a = GoLocalAlias.SimpleLoc(GoRefValue.Local(1, ContextInfo.rootContext))
        val b = GoLocalAlias.SimpleLoc(GoRefValue.Local(2, ContextInfo.rootContext))
        assertTrue(a.compareTo(b) < 0)
    }
}
