package org.opentaint.dataflow.bidi

import kotlinx.serialization.json.*
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.LoopPipelineTrace
import org.opentaint.dataflow.bidi.fixtures.testApManager
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*

class LoopPipelineTraceTest {
    private fun event(line: String): JsonObject =
        Json.parseToJsonElement(line.removePrefix("BIDI_LOOP_PIPELINE_TRACE ")).jsonObject

    private fun internerSizes(ap: ApManager): Map<String, Int> = ApManager::class.java.declaredFields.mapNotNull { field ->
        field.isAccessible = true
        (field.get(ap) as? Map<*, *>)?.let { field.name to it.size }
    }.toMap()

    @Test fun `disabled and unmatched selection never evaluates diagnostic body`() {
        val lines = ArrayList<String>()
        val disabled = LoopPipelineTrace.Recorder(null, lines::add)
        var evaluated = 0
        disabled.record(3, "m", "unused") { evaluated++ }
        val selected = LoopPipelineTrace.Recorder(LoopPipelineTrace.Settings("m", 3, 2), lines::add)
        selected.record(2, "m", "wrong-run") { evaluated++ }
        selected.record(3, "other", "wrong-method") { evaluated++ }
        assertEquals(0, evaluated)
        assertTrue(lines.isEmpty())
        assertEquals(0L, selected.snapshot().attempted)
    }

    @Test fun `complete ND full DAG masks and dictionaries do not intern AP values`() {
        val ap = testApManager(Cancellation())
        val f = ap.accessors.index(FieldAccessor("Box", "f", "Box"))
        val g = ap.accessors.index(FieldAccessor("Box", "g", "Box"))
        val t = ap.marks.mark("T")
        val u = ap.marks.mark("U")
        val v = ap.marks.mark("V")
        val original = ap.premiseOf((0 until 6).map { index ->
            ap.initial(AccessPathBase.Argument(index), ap.path(intArrayOf(f, g)), Tail.STAR,
                ExclusionSet.of(g), MarkSlot.Concrete(if (index % 2 == 0) t else u))
        })
        val exact = ap.taintAlg.leafNode(ap.taintLeaves(MarkSet(intArrayOf(t.id, u.id)), MarkSet.EMPTY))
        val any = ap.taintAlg.leafNode(ap.taintLeaves(MarkSet.EMPTY, MarkSet.of(v)))
        val root = ap.taintAlg.node(TaintLeaves.EMPTY, intArrayOf(f, g), arrayOf(exact, any))
        val protected = ap.taintAlg.node(TaintLeaves.EMPTY, intArrayOf(f), arrayOf(
            ap.taintAlg.leafNode(ap.taintLeaves(MarkSet.of(u), MarkSet.EMPTY))))
        val value = ap.taintTree(AccessPathBase.Argument(0), Layer.NORMAL, root,
            ExclusionSet.of(g), Tail.STAR, protected)
        val flow = ap.flowTree(AccessPathBase.Argument(0), Layer.DEMAND, ExclusionSet.Empty,
            MarkSet(intArrayOf(t.id, u.id)), FlowAlgebra.prepend(ap, ap.path(intArrayOf(f)), FlowAlgebra.LEAF_NODE), Tail.ANY)
        val sizes = internerSizes(ap)
        val lines = ArrayList<String>()
        val trace = LoopPipelineTrace.Recorder(LoopPipelineTrace.Settings("m", 3, 2), lines::add)
        trace.record(3, "m", "full") {
            catalog(ap)
            premise("P", original)
            facts("F", value)
            facts("flow", flow)
            text("escaped", "quote\" newline\n slash\\")
        }
        assertEquals(sizes, internerSizes(ap))
        assertEquals(1L, trace.snapshot().emitted)
        assertEquals(1, lines.size)
        val json = event(lines.single())
        assertEquals(6, json.getValue("P").jsonObject.getValue("members").jsonArray.size)
        assertEquals("quote\" newline\n slash\\", json.getValue("escaped").jsonPrimitive.content)
        val actual = json.getValue("F").jsonObject
        assertEquals("NORMAL", actual.getValue("layer").jsonPrimitive.content)
        assertEquals("STAR", actual.getValue("tail").jsonPrimitive.content)
        assertEquals(listOf(g), actual.getValue("E").jsonArray.map { it.jsonPrimitive.int })
        val nodes = json.getValue("nodes").jsonArray.map { it.jsonObject }.associateBy { it.getValue("id").jsonPrimitive.int }
        val ordinaryRoot = nodes.getValue(actual.getValue("root").jsonPrimitive.int)
        val protectionRoot = nodes.getValue(actual.getValue("protection").jsonPrimitive.int)
        assertEquals(2, ordinaryRoot.getValue("children").jsonArray.size)
        assertEquals(1, protectionRoot.getValue("children").jsonArray.size)
        val ordinaryLeafId = ordinaryRoot.getValue("children").jsonArray.first().jsonObject.getValue("node").jsonPrimitive.int
        val protectedLeafId = protectionRoot.getValue("children").jsonArray.single().jsonObject.getValue("node").jsonPrimitive.int
        assertEquals(listOf(t.id, u.id), nodes.getValue(ordinaryLeafId).getValue("exact").jsonArray.map { it.jsonPrimitive.int })
        assertEquals(listOf(u.id), nodes.getValue(protectedLeafId).getValue("exact").jsonArray.map { it.jsonPrimitive.int })
        assertEquals(listOf(t.id, u.id), json.getValue("flow").jsonObject.getValue("mx").jsonArray.map { it.jsonPrimitive.int })
        assertEquals(setOf(t.id, u.id, v.id), json.getValue("marks").jsonArray.map { it.jsonObject.getValue("id").jsonPrimitive.int }.toSet())
        assertEquals(setOf(f, g), json.getValue("fields").jsonArray.map { it.jsonObject.getValue("id").jsonPrimitive.int }.toSet())
        assertFalse(lines.single().contains("firstBranch"))
    }

    @Test fun `shared DAG node identities are serialized once including shared protection root`() {
        val ap = testApManager(Cancellation())
        val f = ap.accessors.index(FieldAccessor("Box", "f", "Box"))
        val g = ap.accessors.index(FieldAccessor("Box", "g", "Box"))
        val t = ap.marks.mark("T")
        val leaf = ap.taintAlg.leafNode(ap.taintLeaves(MarkSet.of(t), MarkSet.EMPTY))
        val root = ap.taintAlg.node(TaintLeaves.EMPTY, intArrayOf(f, g), arrayOf(leaf, leaf))
        val value = ap.taintTree(AccessPathBase.Argument(0), Layer.NORMAL, root, nonSubsumable = root)
        val lines = ArrayList<String>()
        val trace = LoopPipelineTrace.Recorder(LoopPipelineTrace.Settings("m", 3, 1), lines::add)
        trace.record(3, "m", "shared") { catalog(ap); facts("F", value) }
        val json = event(lines.single())
        assertEquals(2, json.getValue("nodes").jsonArray.size)
        assertEquals(json.getValue("F").jsonObject["root"], json.getValue("F").jsonObject["protection"])
    }

    @Test fun `event and size limits drop whole events and final counters are explicit once`() {
        val lines = ArrayList<String>()
        val trace = LoopPipelineTrace.Recorder(LoopPipelineTrace.Settings("m", 3, 2, maxChars = 256), lines::add)
        trace.record(3, "m", "oversize") { text("payload", "x".repeat(300)) }
        trace.record(3, "m", "small") { flag("ok", true) }
        var afterLimitBody = false
        trace.record(3, "m", "limit") { afterLimitBody = true }
        assertFalse(afterLimitBody)
        trace.finishRun(2)
        trace.finishRun(3)
        trace.finishRun(3)
        val counts = trace.snapshot()
        assertEquals(3L, counts.attempted)
        assertEquals(1L, counts.emitted)
        assertEquals(1L, counts.oversized)
        assertEquals(1L, counts.limitDropped)
        assertEquals(1, lines.count { it.startsWith("BIDI_LOOP_PIPELINE_TRACE ") })
        assertEquals(1, lines.count { it.startsWith("BIDI_LOOP_PIPELINE_TRACE_DROP ") })
        assertEquals(1, lines.count { it.startsWith("BIDI_LOOP_PIPELINE_TRACE_STATS ") })
        assertTrue(lines.last().contains("limitDropped=1"))
        assertTrue(event(lines.single { it.startsWith("BIDI_LOOP_PIPELINE_TRACE ") }).getValue("ok").jsonPrimitive.boolean)
    }

    @Test fun `node cap and logger errors remain bounded diagnostics`() {
        val ap = testApManager(Cancellation())
        val f = ap.accessors.index(FieldAccessor("Box", "f", "Box"))
        val t = ap.marks.mark("T")
        val value = ap.factsOf(PathFact(AccessPathBase.Argument(0), listOf(f), Tail.EXACT, MarkSlot.Concrete(t)), ExclusionSet.Empty, Layer.NORMAL)
        val lines = ArrayList<String>()
        val limited = LoopPipelineTrace.Recorder(LoopPipelineTrace.Settings("m", 3, 1, maxNodes = 1), lines::add)
        limited.record(3, "m", "nodes") { facts("F", value) }
        assertEquals(1L, limited.snapshot().oversized)
        assertFalse(lines.any { it.startsWith("BIDI_LOOP_PIPELINE_TRACE ") })
        val broken = LoopPipelineTrace.Recorder(LoopPipelineTrace.Settings("m", 3, 1)) { error("diagnostic sink unavailable") }
        broken.record(3, "m", "sink") { flag("ok", true) }
        assertEquals(0L, broken.snapshot().emitted)
        assertEquals(1L, broken.snapshot().sinkErrors)
    }

    @Test fun `ZERO dictionary and concrete group token stay explicit`() {
        val ap = testApManager(Cancellation())
        val full = ap.marks.mark("T")
        val group = ap.marks.group(ap.marks.groupOf(full))
        val lines = ArrayList<String>()
        val trace = LoopPipelineTrace.Recorder(LoopPipelineTrace.Settings("m", 3, 1), lines::add)
        trace.record(3, "m", "zero") {
            premise("P", ap.zero)
            facts("F", Reach.DEMAND)
            pattern("group", Pattern(PathFact(AccessPathBase.Argument(0), emptyList(), Tail.ANY, MarkSlot.Concrete(group)), ExclusionSet.Empty))
        }
        val json = event(lines.single())
        assertEquals("ZERO", json.getValue("P").jsonObject.getValue("kind").jsonPrimitive.content)
        assertEquals("CONCRETE", json.getValue("group").jsonObject.getValue("mark").jsonObject.getValue("kind").jsonPrimitive.content)
        val marks = json.getValue("marks").jsonArray.map { it.jsonObject }
        assertTrue(marks.any { it.getValue("id").jsonPrimitive.int == TaintMark.ZERO.id })
        assertTrue(marks.any { it.getValue("id").jsonPrimitive.int == group.id && it.getValue("key").jsonPrimitive.content.contains("Group") })
    }
}
