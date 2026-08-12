package org.opentaint.dataflow.ap.ifds.trace

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class TraceSummarizerTest {
    @Test
    fun `summarizer observes each structurally unique entry once`() {
        val summarizedEntries = arrayListOf<TraceEntry>()
        val summarizer = TraceSummarizer { entry ->
            summarizedEntries.add(entry)
        }
        val entries = MethodTraceResolver.EntryManager(summarizer)

        val final = TraceEntry.Final(emptySet(), statement)
        val equalFinal = TraceEntry.Final(emptySet(), statement)
        val unchanged = TraceEntry.Unchanged(emptySet(), statement)

        assertEquals(entries.entryId(final), entries.entryId(equalFinal))
        entries.entryId(unchanged)

        assertEquals(listOf(final, unchanged), summarizedEntries)
    }

    @Test
    fun `summarizer is optional`() {
        val entries = MethodTraceResolver.EntryManager(traceSummarizer = null)
        val final = TraceEntry.Final(emptySet(), statement)

        assertEquals(0, entries.entryId(final))
    }

    @Test
    fun `metadata requires full resolution exactly when an action may contribute`() {
        val unchangedOnly = TraceMetadataSummarizer().apply {
            summarizeTraceEntry(TraceEntry.Unchanged(emptySet(), statement))
            summarizeTraceEntry(TraceEntry.Final(emptySet(), statement))
        }
        val withAction = TraceMetadataSummarizer().apply {
            summarizeTraceEntry(TraceEntry.Action(emptySet(), statement))
        }

        assertFalse(unchangedOnly.metadata().requiresFullTraceResolution)
        assertTrue(withAction.metadata().requiresFullTraceResolution)
        assertTrue(unchangedOnly.metadata().merge(withAction.metadata()).requiresFullTraceResolution)
    }

    private val statement = object : CommonInst {
        override val location: CommonInstLocation = object : CommonInstLocation {
            override val method: CommonMethod = object : CommonMethod {
                override val name: String = "test"
                override val parameters: List<CommonMethodParameter> = emptyList()
                override val returnType: CommonTypeName = object : CommonTypeName {
                    override val typeName: String = "void"
                }

                override fun flowGraph(): ControlFlowGraph<CommonInst> = object : ControlFlowGraph<CommonInst> {
                    override val instructions: List<CommonInst> = emptyList()
                    override val entries: List<CommonInst> = emptyList()
                    override val exits: List<CommonInst> = emptyList()
                    override fun successors(node: CommonInst): Set<CommonInst> = emptySet()
                    override fun predecessors(node: CommonInst): Set<CommonInst> = emptySet()
                }
            }
        }
    }
}
