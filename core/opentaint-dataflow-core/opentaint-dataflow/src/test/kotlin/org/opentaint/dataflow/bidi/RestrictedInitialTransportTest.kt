package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.EngineShellFixtures
import org.opentaint.dataflow.ifds.UnitResolver
import java.util.concurrent.CopyOnWriteArrayList
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** The real unit protocol carries completed keys without raw caller input. */
class RestrictedInitialTransportTest {
    @Test fun `initial packet copies its keys and rejects empty delivery`(): Unit {
        val f = EngineShellFixtures()
        val initial = f.manager.initial(f.pattern())
        val mutable = arrayListOf(initial)
        val event = RunEvent.InitialsIn(f.b, mutable)
        mutable.clear()
        assertEquals(f.b, event.target())
        assertEquals(listOf(initial), event.initials)
        assertFailsWith<UnsupportedOperationException> { (event.initials as MutableList).clear() }
        assertFailsWith<IllegalArgumentException> { RunEvent.InitialsIn(f.b, emptyList()) }
    }

    @Test fun `same unit delivery is immediate and cross unit delivery keeps a reservation`(): Unit {
        for (sameUnit in listOf(true, false)) {
            val f = EngineShellFixtures()
            val initial = f.manager.initial(f.pattern())
            val observed = CopyOnWriteArrayList<String>()
            lateinit var run: RunManager<ShellActor>
            val resolver = if (sameUnit) UnitResolver { _: org.opentaint.ir.api.common.CommonMethod -> f.unitA }
                else f.unitResolver
            f.shared(threads = 1, unitResolver = resolver).use { shared ->
                val factory = ShellHandlers({ port, event -> when (event) {
                    is RunEvent.Start -> {
                        port.analyzer(event.root)
                        observed += "start"
                        port.startInitials(f.b, listOf(initial))
                        observed += "sent"
                        if (sameUnit) assertEquals(listOf("start", "initial", "sent"), observed)
                        else assertEquals(listOf("start", "sent"), observed)
                    }
                    is RunEvent.InitialsIn -> {
                        assertTrue(run.inFlight.pending > 0)
                        assertEquals(listOf(initial), event.initials)
                        val actor = port.analyzer(event.callee)
                        actor.add(1)
                        assertTrue(port.enqueue(actor))
                        observed += "initial"
                    }
                    else -> error("Only initial transport is used")
                } })
                run = RunManager(f.config(index = 3), shared, factory)
                val result = run.run(5.seconds)
                assertEquals(RunStatus.COMPLETE, result.status)
                assertEquals(0L, run.inFlight.pending)
                assertEquals(if (sameUnit) 3L else 4L, run.inFlight.handled)
                assertEquals(1L, result.analyzers.single { it.key == f.b }.steps)
                assertEquals(if (sameUnit) 1 else 2, factory.ports.size)
                assertFailsWith<IllegalStateException> {
                    factory.ports.first().startInitials(f.b, listOf(initial))
                }
            }
        }
    }

    @Test fun `cancelled initial delivery does not report successful completion`(): Unit {
        val f = EngineShellFixtures()
        val initial = f.manager.initial(f.pattern())
        f.shared().use { shared ->
            val factory = ShellHandlers({ port, event ->
                check(event is RunEvent.Start)
                port.analyzer(event.root)
                f.cancellation.cancel()
                port.startInitials(f.b, listOf(initial))
                error("Cancelled delivery returned")
            })
            val run = RunManager(f.config(index = 3), shared, factory)
            assertEquals(RunStatus.FAILED, run.run(5.seconds).status)
        }
    }

    @Test fun `rejected initial delivery does not complete a run`(): Unit {
        val f = EngineShellFixtures()
        val initial = f.manager.initial(f.pattern())
        f.shared().use { shared ->
            val factory = ShellHandlers({ port, event ->
                check(event is RunEvent.Start)
                port.analyzer(event.root)
                port.startInitials(f.unknown, listOf(initial))
                error("Rejected delivery returned")
            })
            val run = RunManager(f.config(index = 3), shared, factory)
            assertEquals(RunStatus.FAILED, run.run(5.seconds).status)
        }
    }
}
