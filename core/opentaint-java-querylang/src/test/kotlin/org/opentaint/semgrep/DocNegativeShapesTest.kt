package org.opentaint.semgrep

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.TestInstance.Lifecycle.PER_CLASS
import org.opentaint.semgrep.util.SampleBasedTest
import kotlin.test.Test

/**
 * Pins negative-clause anchoring behavior. The failing tests are intentional:
 * their Negative samples assert the desired exclusion semantics, and they stay
 * red while negative clauses do not anchor on argument-position events (or on
 * metavariables without a positive domain). The passing tests are the positive
 * controls proving the same events match positively, and the receiver-position
 * counterparts proving the exclusions work in receiver shape.
 */
@TestInstance(PER_CLASS)
class DocNegativeShapesTest : SampleBasedTest() {

    @Test
    fun `test sanitize pattern-not`() = runTest<example.SanitizePatternNotDoc>()

    @Test
    fun `test argument observer pattern-not`() = runTest<example.ArgObserverPatternNotDoc>()

    @Test
    fun `test allowlist pattern-not-inside`() = runTest<example.AllowlistNotInsideDoc>()

    @Test
    fun `test negative-only metavariables`() = runTest<example.NegOnlyNotInsideDoc>()

    @Test
    fun `test receiver sanitize pattern-not`() = runTest<example.ReceiverSanitizePatternNotDoc>()

    @Test
    fun `test argument full-form pattern-not`() = runTest<example.ArgFullPatternNotDoc>()

    @Test
    fun `test argument event matches positively`() = runTest<example.ArgEventSanityDoc>()

    @Test
    fun `test instance argument pattern-not-inside`() = runTest<example.InstanceArgNotInsideDoc>()

    @Test
    fun `test sanitize reassignment event matches positively`() = runTest<example.SanitizeEventSanityDoc>()

    @Test
    fun `test sanitize reassignment pattern-not-inside`() = runTest<example.SanitizeNotInsideDoc>()

    @Test
    fun `test argument not-inside with satisfiable containment`() = runTest<example.ArgNotInsideAnchoredDoc>()

    @Test
    fun `test receiver not-inside against multi-event main pattern`() = runTest<example.ReceiverNotInsideSpanDoc>()

    @AfterAll
    fun close() {
        closeRunner()
    }
}
