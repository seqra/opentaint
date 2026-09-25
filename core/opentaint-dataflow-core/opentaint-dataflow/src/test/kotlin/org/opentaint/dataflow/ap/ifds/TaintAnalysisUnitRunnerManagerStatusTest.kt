package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.util.analysis.ApplicationGraph
import java.lang.reflect.Proxy
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse

/**
 * The failure status ordering of [TaintAnalysisUnitRunnerManager] (spec §10, M7): a phase that
 * awaits the analysis reads [TaintAnalysisUnitRunnerManager.status] as soon as the analysis
 * completes, so every stop path must set the status before it completes the analysis. Each test
 * reads the status in a completion handler, which runs on the completing thread at the moment of
 * completion.
 */
class TaintAnalysisUnitRunnerManagerStatusTest {
    /** An interface instance whose every call fails: the stop paths under test never call it. */
    private inline fun <reified T : Any> unused(): T = Proxy.newProxyInstance(
        T::class.java.classLoader, arrayOf(T::class.java)
    ) { _, method, _ -> error("unexpected call to ${method.name}") } as T

    private fun manager() = TaintAnalysisUnitRunnerManager(
        RefManager(), Cancellation(),
        unused<TaintAnalysisManager>(),
        unused<ApplicationGraph<CommonMethod, CommonInst>>(),
        unused<UnitResolver<CommonMethod>>(),
        unused<SummarySerializationContext>(),
        taintRulesStatsSamplingPeriod = null,
    )

    /** The status at the moment the current analysis completes, or `null` if it has not. */
    private fun TaintAnalysisUnitRunnerManager.statusAtCompletion(): () -> TaintAnalysisUnitRunnerManager.Status? {
        var observed: TaintAnalysisUnitRunnerManager.Status? = null
        invokeOnAnalysisCompletion { observed = status.get() }
        return { observed }
    }

    @Test
    fun `the low-memory stop sets OOM before it completes the analysis`() = manager().use { manager ->
        val atCompletion = manager.statusAtCompletion()

        manager.stopOnLowMemory()

        assertEquals(TaintAnalysisUnitRunnerManager.Status.OOM, atCompletion())
        assertFalse(manager.cancellation.isActive())
    }

    @Test
    fun `a runner exception sets EXCEPTION before it completes the analysis`() = manager().use { manager ->
        val atCompletion = manager.statusAtCompletion()

        manager.stopOnRunnerException(UnknownUnit, IllegalStateException("runner failed"))

        assertEquals(TaintAnalysisUnitRunnerManager.Status.EXCEPTION, atCompletion())
    }

    @Test
    fun `a cancelled runner neither completes the analysis nor changes the status`() = manager().use { manager ->
        val atCompletion = manager.statusAtCompletion()

        manager.stopOnRunnerException(UnknownUnit, Cancellation.Cancelled())

        assertEquals(null, atCompletion())
        assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, manager.status.get())
    }

    @Test
    fun `the first failure status wins`() = manager().use { manager ->
        manager.stopOnRunnerException(UnknownUnit, IllegalStateException("runner failed"))
        manager.stopOnLowMemory()

        assertEquals(TaintAnalysisUnitRunnerManager.Status.EXCEPTION, manager.status.get())
        assertFalse(manager.cancellation.isActive())
    }
}
