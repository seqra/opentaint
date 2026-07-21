package org.opentaint.python.sast.dataflow

import io.mockk.every
import io.mockk.mockk
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.python.analysis.PIRMethodCallFactMapper
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRCallArg
import org.opentaint.ir.api.python.PIRCallArgKind
import org.opentaint.ir.api.python.PIRClass
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRLocation
import org.opentaint.ir.api.python.PIRParameter
import org.opentaint.ir.api.python.PIRParameterKind
import org.opentaint.ir.api.python.PIRStrConst
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull

/**
 * Unit-level coverage for the keyword-aware frame arithmetic in [PIRMethodCallFactMapper].
 * The `toCallerFrame` keyword back-map and its POSITIONAL guard have no end-to-end path yet
 * (they serve callee→caller mutation flow, which is future work), so they are pinned here.
 */
class PIRMethodCallFactMapperTest {

    // --- toCalleeFrame ---

    @Test
    fun `toCalleeFrame binds a keyword arg to its named parameter, ignoring position`() {
        // out-of-order: kw(b) at raw slot 0 must land on param b (index 1), not positional slot 0
        val call = call(kw("b"), kw("a"))
        val callee = moduleFunction("a", "b")
        assertEquals(AccessPathBase.Argument(1), PIRMethodCallFactMapper.toCalleeFrame(call, callee, arg(0)))
    }

    @Test
    fun `toCalleeFrame drops a keyword matching no explicit parameter`() {
        val call = call(kw("missing"))
        val callee = moduleFunction("a")
        assertNull(PIRMethodCallFactMapper.toCalleeFrame(call, callee, arg(0)))
    }

    @Test
    fun `toCalleeFrame shifts positional args by the implicit self offset`() {
        val call = call(pos())
        val callee = instanceMethod("self", "a")
        assertEquals(AccessPathBase.Argument(1), PIRMethodCallFactMapper.toCalleeFrame(call, callee, arg(0)))
        assertEquals(AccessPathBase.Argument(0), PIRMethodCallFactMapper.toCalleeFrame(call, callee, AccessPathBase.This))
    }

    // --- toCallerFrame (the branches with no end-to-end coverage) ---

    @Test
    fun `toCallerFrame maps a callee parameter back to its keyword arg slot`() {
        // param b (index 1) is filled by kw(b) at raw slot 0 → exit fact on Argument(1) returns Argument(0)
        val call = call(kw("b"), kw("a"))
        val callee = moduleFunction("a", "b")
        assertEquals(AccessPathBase.Argument(0), PIRMethodCallFactMapper.toCallerFrame(call, callee, arg(1)))
    }

    @Test
    fun `toCallerFrame drops an unfilled parameter that would rebase onto a keyword slot`() {
        // param b (index 1) is an unpassed default; raw slot 1 is kw(c), not positional → must not leak
        val call = call(pos(), kw("c"))
        val callee = moduleFunction("a", "b", "c")
        assertNull(PIRMethodCallFactMapper.toCallerFrame(call, callee, arg(1)))
    }

    @Test
    fun `toCallerFrame maps a positional parameter back to its raw slot`() {
        val call = call(pos(), pos())
        val callee = moduleFunction("a", "b")
        assertEquals(AccessPathBase.Argument(1), PIRMethodCallFactMapper.toCallerFrame(call, callee, arg(1)))
    }

    @Test
    fun `toCallerFrame maps the implicit first parameter back to the receiver marker`() {
        val call = call(pos())
        val callee = instanceMethod("self", "a")
        assertEquals(AccessPathBase.This, PIRMethodCallFactMapper.toCallerFrame(call, callee, arg(0)))
    }

    // --- helpers ---

    private fun arg(idx: Int): AccessPathBase = AccessPathBase.Argument(idx)

    private fun call(vararg args: PIRCallArg): PIRCall =
        PIRCall(target = null, callee = PIRStrConst("callee"), args = args.toList(), location = unusedLocation)

    private fun pos(): PIRCallArg = PIRCallArg(PIRStrConst("x"), PIRCallArgKind.POSITIONAL)
    private fun kw(name: String): PIRCallArg = PIRCallArg(PIRStrConst("x"), PIRCallArgKind.KEYWORD, name)

    private fun moduleFunction(vararg paramNames: String): PIRFunction = mockk {
        every { parameters } returns paramNames.mapIndexed(::param)
        every { enclosingClass } returns null
        every { isStaticMethod } returns false
    }

    private fun instanceMethod(vararg paramNames: String): PIRFunction = mockk {
        every { parameters } returns paramNames.mapIndexed(::param)
        every { enclosingClass } returns mockk<PIRClass>()
        every { isStaticMethod } returns false
    }

    private fun param(index: Int, name: String): PIRParameter = mockk {
        every { this@mockk.name } returns name
        every { this@mockk.index } returns index
        every { this@mockk.kind } returns PIRParameterKind.POSITIONAL_OR_KEYWORD
    }

    private val unusedLocation = object : PIRLocation {
        override val method: PIRFunction get() = error("location is never read by the frame mappers")
        override val index: Int = 0
    }
}
