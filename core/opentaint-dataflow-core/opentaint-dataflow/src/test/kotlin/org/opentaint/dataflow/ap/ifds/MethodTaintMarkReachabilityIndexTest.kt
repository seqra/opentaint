package org.opentaint.dataflow.ap.ifds

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class MethodTaintMarkReachabilityIndexTest {
    @Test
    fun `finds direct and transitive callers`() {
        val index = MethodTaintMarkReachabilityIndex<String>()
        index.addCall("entry", "controller")
        index.addCall("controller", "sink")
        index.addCall("unrelated", "other")

        assertEquals(setOf("sink", "controller", "entry"), index.methodsThatCanReach("sink"))
    }

    @Test
    fun `uses summary mark transformation between calls`() {
        val index = MethodTaintMarkReachabilityIndex<String>()
        index.addCall("entry", "transform")
        index.addCall("transform", "sink")
        index.recordInputMark("transform", "raw")
        index.recordExactSummary("transform", "raw", "encoded")
        index.recordInputMark("sink", "encoded")

        val reachable = index.statesThatCanReach(
            "sink",
            setOf("encoded"),
            emptyMap(),
            relevantMarks = setOf("raw", "encoded"),
        )

        assertTrue(MethodTaintMarkState("entry", "raw") in reachable)
        assertFalse(MethodTaintMarkState("entry", "unrelated") in reachable)
    }

    @Test
    fun `summary without taint marks does not create mark reachability`() {
        val index = MethodTaintMarkReachabilityIndex<String>()
        index.addCall("entry", "pass")
        index.addCall("pass", "sink")
        index.recordSummary("pass", emptySet(), emptySet())
        index.recordInputMark("sink", "tainted")

        val reachable = index.statesThatCanReach(
            "sink",
            setOf("tainted"),
            emptyMap(),
            relevantMarks = setOf("tainted"),
        )

        assertFalse(MethodTaintMarkState("entry", "tainted") in reachable)
        assertEquals(1, index.stats().methods)
    }

    @Test
    fun `uses rule transitions inside a method`() {
        val index = MethodTaintMarkReachabilityIndex<String>()
        index.addCall("entry", "sink")
        index.recordInputMark("sink", "validated")

        val reachable = index.statesThatCanReach(
            targetMethod = "sink",
            targetMarks = setOf("validated"),
            ruleTransitions = mapOf(
                "entry" to setOf(TaintMarkTransition("raw", "validated")),
            ),
            relevantMarks = setOf("raw", "validated"),
        )

        assertTrue(MethodTaintMarkState("entry", "raw") in reachable)
    }

    @Test
    fun `ignores summary marks outside the vulnerability rule graph`() {
        val index = MethodTaintMarkReachabilityIndex<String>()
        index.addCall("entry", "transform")
        index.addCall("transform", "sink")
        index.recordExactSummary("transform", "raw", "validated")
        index.recordExactSummary("transform", "unrelated", "validated")
        index.recordInputMark("sink", "validated")

        val reachable = index.statesThatCanReach(
            targetMethod = "sink",
            targetMarks = setOf("validated"),
            ruleTransitions = emptyMap(),
            relevantMarks = setOf("raw", "validated"),
        )

        assertTrue(MethodTaintMarkState("transform", "raw") in reachable)
        assertTrue(MethodTaintMarkState("entry", "raw") in reachable)
        assertFalse(MethodTaintMarkState("transform", "unrelated") in reachable)
        assertFalse(MethodTaintMarkState("entry", "unrelated") in reachable)
    }

    @Test
    fun `ignores rule transitions outside the vulnerability rule graph`() {
        val index = MethodTaintMarkReachabilityIndex<String>()
        index.addCall("entry", "sink")
        index.recordInputMark("sink", "validated")

        val reachable = index.statesThatCanReach(
            targetMethod = "sink",
            targetMarks = setOf("validated"),
            ruleTransitions = mapOf(
                "entry" to setOf(
                    TaintMarkTransition("raw", "validated"),
                    TaintMarkTransition("unrelated", "validated"),
                ),
            ),
            relevantMarks = setOf("raw", "validated"),
        )

        assertTrue(MethodTaintMarkState("entry", "raw") in reachable)
        assertFalse(MethodTaintMarkState("entry", "unrelated") in reachable)
    }
}
