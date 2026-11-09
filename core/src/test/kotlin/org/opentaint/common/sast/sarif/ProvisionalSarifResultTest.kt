package org.opentaint.common.sast.sarif

import io.github.detekt.sarif4k.Level
import io.github.detekt.sarif4k.Message
import io.github.detekt.sarif4k.PropertyBag
import io.github.detekt.sarif4k.Result
import kotlinx.serialization.json.Json
import org.junit.jupiter.api.Test
import kotlin.test.assertEquals
import kotlin.test.assertSame
import kotlin.test.assertTrue

class ProvisionalSarifResultTest {
    private fun finding() = Result(
        ruleID = "path-traversal",
        message = Message(text = "Tainted path", markdown = "**Tainted path**"),
        level = Level.Warning,
        partialFingerprints = mapOf("vulnerabilitySinkHash/v1" to "stable-location"),
        properties = PropertyBag(tags = listOf("existing-tag")),
    )

    @Test
    fun `confirmed output is unchanged`() {
        val original = finding()
        assertSame(original, original.withProvisionalFinding(false))
    }

    @Test
    fun `provisional output keeps identity and adds a visible refinement warning`() {
        val original = finding()
        val marked = original.withProvisionalFinding(true)
        assertEquals(original.ruleID, marked.ruleID)
        assertEquals(original.partialFingerprints, marked.partialFingerprints)
        assertEquals(original.level, marked.level)
        assertEquals(listOf("existing-tag", "opentaint:provisional"), marked.properties?.tags)
        assertTrue(marked.message.text.orEmpty().contains("Later refinement may discard this finding."))
        assertTrue(marked.message.markdown.orEmpty().contains("Later refinement may discard this finding."))
    }

    @Test
    fun `provisional tag and warning survive SARIF JSON serialization`() {
        val json = Json.encodeToString(Result.serializer(), finding().withProvisionalFinding(true))
        assertTrue(json.contains("opentaint:provisional"))
        assertTrue(json.contains("Later refinement may discard this finding."))
        assertTrue(json.contains("stable-location"))
    }
}
