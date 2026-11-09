package org.opentaint.jvm.sast.project

import ch.qos.logback.classic.Logger
import ch.qos.logback.classic.spi.ILoggingEvent
import ch.qos.logback.core.read.ListAppender
import org.opentaint.common.sast.dataflow.TaintAnalyzerOptions
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.bidi.driver.IncreasingLimits
import org.opentaint.ir.api.jvm.JIRClassOrInterface
import org.opentaint.ir.api.jvm.RegisteredLocation
import org.opentaint.jvm.sast.ast.BasicTestUtils
import org.opentaint.jvm.sast.dataflow.ClassLocationChecker
import org.opentaint.jvm.sast.dataflow.JIRTaintAnalyzer
import org.opentaint.jvm.sast.dataflow.JIRTaintRulesProvider
import org.opentaint.jvm.sast.dataflow.rules.TaintConfiguration
import org.slf4j.LoggerFactory
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.time.Duration.Companion.seconds

class BidiIterationLimitOptionTest : BasicTestUtils() {
    override val sourceFileExtension = "java"

    @Test
    fun `legacy cap is isolated from bidi options and diagnosed once per analyzer`() {
        val logger = LoggerFactory.getLogger(JIRTaintAnalyzer::class.java) as Logger
        val events = ListAppender<ILoggingEvent>().apply { start() }
        logger.addAppender(events)
        val locations = object : ClassLocationChecker {
            override fun isProjectLocation(loc: RegisteredLocation) = true
            override fun isProjectClass(cls: JIRClassOrInterface) = true
        }
        try {
            for (bidi in listOf(false, true)) for (cap in listOf(null, 0, 1, 1000)) {
                events.list.clear()
                val requested = TaintAnalyzerOptions(17.seconds, ApMode.Tree, iterationLimit = cap)
                JIRTaintAnalyzer(cp, JIRTaintRulesProvider(TaintConfiguration(cp)), locations,
                    requested, bidiPolicy = if (bidi) IncreasingLimits else null).use { analyzer ->
                    assertEquals(if (bidi) requested.copy(iterationLimit = null) else requested, analyzer.options)
                    if (bidi) {
                        assertEquals(listOf(1, 1, 2, 3), (1..4).map { analyzer.bidiPolicy!!.fieldLimit(it) })
                        // Reading the effective options must not add another diagnostic.
                        repeat(3) { assertEquals(null, analyzer.options.iterationLimit) }
                    }
                    assertEquals(if (bidi && cap != null) 1 else 0,
                        events.list.count { it.formattedMessage.contains("--iteration-limit is ignored") })
                }
            }
        } finally {
            logger.detachAppender(events)
            events.stop()
        }
    }
}
