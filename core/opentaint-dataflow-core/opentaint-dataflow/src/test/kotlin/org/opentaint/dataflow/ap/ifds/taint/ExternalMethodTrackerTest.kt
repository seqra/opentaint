package org.opentaint.dataflow.ap.ifds.taint

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class ExternalMethodTrackerTest {
    private fun ExternalMethodTracker.reported(): List<String> =
        getExternalMethods().let { it.withoutRules + it.withRules }.map { it.method }

    @Test
    fun `an unmodelled method is reported`() {
        val tracker = ExternalMethodTracker()
        tracker.trackExternalMethod(SAM, DESC, "arg0", rulesApplied = false)

        assertEquals(listOf(SAM), tracker.reported())
    }

    @Test
    fun `untracking removes a method already recorded at an earlier call site`() {
        // The resolver may reach a SAM call site only after another call site has
        // already recorded the method, so untracking has to erase the existing
        // record rather than merely suppress later ones.
        val tracker = ExternalMethodTracker()
        tracker.trackExternalMethod(SAM, DESC, "arg0", rulesApplied = false)
        assertTrue(SAM in tracker.reported())

        tracker.untrackMethod(SAM, DESC)

        assertEquals(emptyList(), tracker.reported())
    }

    @Test
    fun `untracking suppresses every later call site of that method`() {
        val tracker = ExternalMethodTracker()
        tracker.untrackMethod(SAM, DESC)

        tracker.trackExternalMethod(SAM, DESC, "arg0", rulesApplied = false)
        tracker.trackExternalMethod(SAM, DESC, "arg1", rulesApplied = true)

        assertEquals(emptyList(), tracker.reported())
    }

    @Test
    fun `untracking is keyed by signature, not by name alone`() {
        val tracker = ExternalMethodTracker()
        tracker.trackExternalMethod(SAM, DESC, "arg0", rulesApplied = false)
        tracker.trackExternalMethod(SAM, OTHER_DESC, "arg0", rulesApplied = false)

        tracker.untrackMethod(SAM, DESC)

        // the other overload is a different method and must still be reported
        assertEquals(listOf(SAM), tracker.reported())
    }

    private companion object {
        const val SAM = "java.util.function.Function#apply"
        const val DESC = "(Ljava/lang/Object;)Ljava/lang/Object;"
        const val OTHER_DESC = "(Ljava/lang/String;)Ljava/lang/Object;"
    }
}
