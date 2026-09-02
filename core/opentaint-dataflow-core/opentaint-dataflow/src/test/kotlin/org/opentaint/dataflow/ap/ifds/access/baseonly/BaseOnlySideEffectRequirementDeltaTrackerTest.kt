package org.opentaint.dataflow.ap.ifds.access.baseonly

import kotlinx.collections.immutable.persistentHashSetOf
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull

class BaseOnlySideEffectRequirementDeltaTrackerTest {
    private val manager = BaseOnlyApManager(
        AnyAccessorUnrollStrategy.AnyAccessorDisabled,
        Cancellation(),
        fieldSensitive = true,
    )
    private val first = TaintMarkAccessor("first")
    private val second = TaintMarkAccessor("second")

    private fun fact(
        access: BaseOnlyAccess = ABSTRACT_EMPTY_ACCESS,
        exclusions: ExclusionSet = ExclusionSet.Empty,
    ): InitialFactAp = BaseOnlyInitialFactAp(manager, AccessPathBase.This, access, exclusions)

    private fun exclusions(vararg marks: TaintMarkAccessor): ExclusionSet =
        ExclusionSet.Concrete(persistentHashSetOf(*marks))

    @Test
    fun `first requirement is retained including an empty exclusion`() {
        val tracker = BaseOnlySideEffectRequirementDeltaTracker()
        val current = fact()
        val requirement = fact()

        assertEquals(requirement, tracker.add(current, requirement))
        assertNull(tracker.add(current, requirement))
    }

    @Test
    fun `growing requirement publishes only newly added exclusions`() {
        val tracker = BaseOnlySideEffectRequirementDeltaTracker()
        val current = fact()

        assertEquals(exclusions(first), tracker.add(current, fact(exclusions = exclusions(first)))?.exclusions)
        assertEquals(
            exclusions(second),
            tracker.add(current, fact(exclusions = exclusions(first, second)))?.exclusions,
        )
        assertNull(tracker.add(current, fact(exclusions = exclusions(first, second))))
    }

    @Test
    fun `different access operations keep independent exclusion state`() {
        val tracker = BaseOnlySideEffectRequirementDeltaTracker()
        val current = fact()
        val otherAccess = manager.finalAccessorAccess

        assertEquals(exclusions(first), tracker.add(current, fact(exclusions = exclusions(first)))?.exclusions)
        assertEquals(
            exclusions(first),
            tracker.add(current, fact(otherAccess, exclusions(first)))?.exclusions,
        )
    }

    @Test
    fun `universe is published once after a concrete exclusion`() {
        val tracker = BaseOnlySideEffectRequirementDeltaTracker()
        val current = fact()

        assertEquals(exclusions(first), tracker.add(current, fact(exclusions = exclusions(first)))?.exclusions)
        assertEquals(
            ExclusionSet.Universe,
            tracker.add(current, fact(exclusions = ExclusionSet.Universe))?.exclusions,
        )
        assertNull(tracker.add(current, fact(exclusions = exclusions(first, second))))
        assertNull(tracker.add(current, fact(exclusions = ExclusionSet.Universe)))
    }

    @Test
    fun `empty state accepts the first later concrete exclusion`() {
        val tracker = BaseOnlySideEffectRequirementDeltaTracker()
        val current = fact()

        assertEquals(ExclusionSet.Empty, tracker.add(current, fact())?.exclusions)
        assertEquals(exclusions(first), tracker.add(current, fact(exclusions = exclusions(first)))?.exclusions)
    }
}
