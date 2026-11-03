package org.opentaint.dataflow.jvm.bidi

import org.opentaint.dataflow.bidi.ap.Direction
import org.opentaint.dataflow.graph.BlockLiveLocals
import org.opentaint.dataflow.graph.CompactGraph
import org.opentaint.dataflow.graph.LocalAccess
import org.opentaint.dataflow.graph.MethodBlockLayoutBuilder
import org.opentaint.dataflow.jvm.bidi.interp.localAccess
import org.opentaint.dataflow.jvm.bidi.interp.JIRMethodEntries
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.ir.api.jvm.JIRField
import org.opentaint.ir.api.jvm.JIRTypedField
import org.opentaint.ir.api.jvm.cfg.*
import org.opentaint.ir.api.jvm.ext.cfg.callExpr
import java.util.BitSet
import java.lang.reflect.Proxy
import kotlin.test.*

class JIRBlockLiveLocalsTest : BidiJIRTestUtils() {
    private fun bits(vararg indices: Int) = BitSet().apply { indices.forEach(::set) }

    /** Check the old value at an assignment, including a later use of its result. */
    private fun liveBefore(inst: JIRInst, vararg laterReads: Int): BlockLiveLocals {
        val forward = CompactGraph.build(2) { if (it == 0) bits(1) else bits() }
        val backward = CompactGraph.build(2) { if (it == 1) bits(0) else bits() }
        val layout = MethodBlockLayoutBuilder.build(forward, listOf(0))
        val read = bits(*laterReads)
        return BlockLiveLocals.build(layout, forward, backward,
            listOf(localAccess(inst), LocalAccess(read, bits(), read)), manager.cancellation)
    }

    private fun location() = method("copy").instList.instructions.filterIsInstance<JIRAssignInst>().first().location
    private fun locals(): Pair<JIRLocalVar, JIRLocalVar> {
        val value = method("copy").instList.instructions.filterIsInstance<JIRAssignInst>().first().lhv
        return JIRLocalVar(501, "tmp", value.type) to JIRLocalVar(502, "x", value.type)
    }

    @Test fun `copy excludes lhs from reads and kills its old value even before a later read`() {
        val (tmp, x) = locals()
        val mask = liveBefore(JIRAssignInst(location(), tmp, x), tmp.index)
        assertFalse(mask.mayEnter(false, 0, tmp.index), "tmp=x overwrites old tmp before observe(tmp)")
        assertTrue(mask.mayEnter(false, 0, x.index), "The RHS value supplies the new tmp")
        assertTrue(mask.mayEnter(true, 1, tmp.index), "Backward keeps the assignment lhs")
        assertTrue(mask.mayEnter(true, 1, x.index), "Backward does not kill the rhs")
    }

    @Test fun `self copy reads before its definite overwrite`() {
        val (tmp, _) = locals()
        assertTrue(liveBefore(JIRAssignInst(location(), tmp, tmp)).mayEnter(false, 0, tmp.index))
    }

    @Test fun `constant copies kill but throwing or unknown rhs does not certify a kill`() {
        val (tmp, x) = locals()
        assertFalse(liveBefore(JIRAssignInst(location(), tmp, JIRNullConstant(tmp.type)), tmp.index)
            .mayEnter(false, 0, tmp.index))
        for (rhs in listOf(JIRCastExpr(tmp.type, x), JIRNewExpr(tmp.type))) {
            assertTrue(liveBefore(JIRAssignInst(location(), tmp, rhs), tmp.index)
                .mayEnter(false, 0, tmp.index), "Uncertain commit must preserve the old value on exceptional routes")
        }
    }

    @Test fun `memory lhs reads its address and index without killing the base`() {
        val (array, index) = locals()
        val write = JIRAssignInst(location(), JIRArrayAccess(array, index, array.type), JIRNullConstant(array.type))
        val mask = liveBefore(write)
        assertTrue(mask.mayEnter(false, 0, array.index))
        assertTrue(mask.mayEnter(false, 0, index.index))
        val ret = JIRReturnInst(location(), array)
        assertTrue(liveBefore(ret).mayEnter(false, 0, array.index))
    }

    @Test fun `operand extraction does not resolve field declarations`() {
        val original = method("staticRead").instList.instructions.filterIsInstance<JIRAssignInst>()
            .first { it.rhv is JIRFieldRef }
        val ref = original.rhv as JIRFieldRef
        val unresolved = object : JIRTypedField by ref.field {
            override val field: JIRField get() = error("Boundary liveness must not resolve fields")
        }
        val (tmp, _) = locals()
        assertTrue(liveBefore(JIRAssignInst(original.location, tmp, JIRFieldRef(null, unresolved)), tmp.index)
            .mayEnter(false, 0, tmp.index), "Field reads keep unknown-commit lhs values")
    }

    @Test fun `real loop keeps a coalesced output register and a live carried value`() {
        val owner = "sample.bidi.BidiBoundaryLocalsSample"
        val copies = entries[method("copies", owner)]
        val assignments = method("copies", owner).instList.instructions.filterIsInstance<JIRAssignInst>()
        val copy = assignments.single { (it.lhv as? JIRLocalVar)?.name == "tmp" }
        val tmp = assertIs<JIRLocalVar>(copy.lhv)
        // IR lowering coalesces x and tmp. This actual register remains live
        // at return x, so its source-level tmp name must not cause a drop.
        assertIs<JIRCallExpr>(copy.rhv)
        val loop = copies.blockLayout.blocks.single { it.isLoop }
        assertTrue(loop.repeatPorts.isNotEmpty())
        for (port in loop.repeatPorts) {
            val physical = copies.blockLayout.ports[port.ordinal]
            val route = copies.blockLayout.route(physical.from, physical.to)
            assertTrue(copies.blockLiveLocals.mayFollow(false, route, tmp.index))
        }
        val carriedMethod = method("carried", owner)
        val carried = entries[carriedMethod]
        val reader = carriedMethod.instList.instructions.mapNotNull { it.callExpr }
            .single { it.method.name == "observe" }
        val carriedTmp = assertIs<JIRLocalVar>(reader.args.single())
        for (port in carried.blockLayout.blocks.single { it.isLoop }.repeatPorts) {
            val physical = carried.blockLayout.ports[port.ordinal]
            assertTrue(carried.blockLiveLocals.mayFollow(false,
                carried.blockLayout.route(physical.from, physical.to), carriedTmp.index),
                "port=$physical local=$carriedTmp/${carriedTmp.index}\n" +
                    carriedMethod.instList.instructions.joinToString("\n") { "${it.location.index}: $it" })
        }
    }

    @Test fun `one method owns immutable direction metadata without initializing aliases`() {
        val method = method("copies", "sample.bidi.BidiBoundaryLocalsSample")
        val entry = entries[method]
        val field = entry.javaClass.getDeclaredField("aliasAnalysis\$delegate").apply { isAccessible = true }
        val lazyAlias = field.get(entry) as Lazy<*>
        assertFalse(lazyAlias.isInitialized())
        val cache = JIRMethodContextCache(interp, entries)
        assertSame(entry.blockLiveLocals, cache.blockLiveLocals(key(method)))
        assertSame(entry.blockLiveLocals, cache.blockLiveLocals(key(method)))
        assertSame(entry.graph(Direction.FORWARD), cache.graph(key(method), Direction.FORWARD))
        assertFalse(lazyAlias.isInitialized(), "The pure CFG sidecar must not run alias analysis")
    }

    @Test fun `building both direction masks never queries the rule provider`() {
        val forbidden = Proxy.newProxyInstance(TaintRulesProvider::class.java.classLoader,
            arrayOf(TaintRulesProvider::class.java)) { _, call, _ ->
            error("Instruction-only liveness must not query ${call.name}")
        } as TaintRulesProvider
        val owner = JIRMethodEntries(graph, languageManager, callResolver, forbidden,
            JIRLocalAliasAnalysis.Params(useAliasAnalysis = true), manager.cancellation, emptyMap())
        val entry = owner[method("copies", "sample.bidi.BidiBoundaryLocalsSample")]
        assertSame(entry.blockLiveLocals, entry.blockLiveLocals)
    }
}
