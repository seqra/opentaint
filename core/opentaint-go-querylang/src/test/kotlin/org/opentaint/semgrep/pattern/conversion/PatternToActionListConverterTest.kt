package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.SemgrepGoPattern
import org.opentaint.semgrep.pattern.SemgrepGoPatternParser
import org.opentaint.semgrep.pattern.SemgrepGoPatternParsingResult
import kotlin.test.Test
import kotlin.test.assertNull
import kotlin.test.assertTrue

class PatternToActionListConverterTest {
    private val parser = SemgrepGoPatternParser()

    private fun parse(src: String): SemgrepGoPattern {
        val r = parser.parseSemgrepGoPattern(src)
        check(r is SemgrepGoPatternParsingResult.Ok) { "parse failed for `$src`: $r" }
        return r.pattern
    }

    private fun convert(src: String): Pair<SemgrepGoPatternActionList?, Map<String, Int>> {
        val c = PatternToActionListConverter()
        return c.createActionList(parse(src)) to c.failedTransformations
    }

    @Test fun unsupportedReturnsNullAndRecordsReason() {
        val (result, failures) = convert("if true { }")
        assertNull(result)
        assertTrue(failures.isNotEmpty(), "expected a recorded failure reason, got $failures")
    }
}
