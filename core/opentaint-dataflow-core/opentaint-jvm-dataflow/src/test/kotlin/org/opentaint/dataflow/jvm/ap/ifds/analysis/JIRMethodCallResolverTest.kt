package org.opentaint.dataflow.jvm.ap.ifds.analysis

import io.mockk.mockk
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRVirtualCallExpr

class JIRMethodCallResolverTest {
    private val concrete
        get() = JIRCallResolver.MethodResolutionResult.ConcreteMethod(mockk<MethodWithContext>())

    private val lambda
        get() = JIRCallResolver.MethodResolutionResult.Lambda(
            mockk<JIRVirtualCallExpr>(),
            mockk<JIRMethod>(),
        )

    private val failed
        get() = JIRCallResolver.MethodResolutionResult.MethodResolutionFailed

    @Test
    fun `resolved SAM fallback is not classified as an external method`() {
        assertTrue(listOf(concrete, lambda).hasResolvedSamFallback())
    }

    @Test
    fun `a resolution failure means the call is not fully resolved`() {
        assertFalse(listOf(concrete, lambda, failed).hasResolvedSamFallback())
    }

    @Test
    fun `a concrete target with no lambda is an ordinary virtual call`() {
        // Not a SAM fallback: nothing was dispatched through a functional interface,
        // so the method must stay tracked if it is otherwise unmodelled.
        assertFalse(listOf(concrete).hasResolvedSamFallback())
        assertFalse(listOf(concrete, concrete).hasResolvedSamFallback())
    }

    @Test
    fun `a lambda with no concrete target is not a fallback either`() {
        assertFalse(listOf(lambda).hasResolvedSamFallback())
        assertFalse(listOf(lambda, lambda).hasResolvedSamFallback())
    }

    @Test
    fun `an unresolved call is not a fallback`() {
        assertFalse(emptyList<JIRCallResolver.MethodResolutionResult>().hasResolvedSamFallback())
        assertFalse(listOf(failed).hasResolvedSamFallback())
    }
}
