package org.opentaint.jvm.sast.dataflow

import org.opentaint.common.sast.CommonAnalysisOptions
import org.opentaint.common.sast.dataflow.MarkSetScanOptions
import org.opentaint.common.sast.dataflow.TaintAnalyzerOptions
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.minutes

/** The mark-set shallow scan is on by default, in the best known configuration (spec §2). */
class MarkSetScanOptionsDefaultsTest {
    @Test
    fun `the mark-set scan is enabled by default, flow-insensitive, with relevance and without relaxed conditions`() {
        val defaults = MarkSetScanOptions()
        assertTrue(defaults.enabled, "the mark-set scan is off by default")
        assertEquals(false, defaults.relaxed, "option 4* is on by default")
        assertEquals(true, defaults.relevance, "relevance pruning is off by default")
        assertEquals(false, defaults.flowSensitive, "option 3* is on by default")
    }

    @Test
    fun `a TaintAnalyzerOptions built without markSet gets the enabled default`() {
        val options = TaintAnalyzerOptions(ifdsTimeout = 1.minutes, ifdsApMode = org.opentaint.dataflow.ap.ifds.access.ApMode.Tree)
        assertEquals(MarkSetScanOptions(), options.markSet)
        assertTrue(options.markSet.enabled)
    }

    @Test
    fun `a CommonAnalysisOptions built without markSet carries the enabled default into TaintAnalyzerOptions`() {
        val common = CommonAnalysisOptions()
        assertTrue(common.markSet.enabled)
        assertTrue(common.taintAnalyzerOptions().markSet.enabled)
    }
}
