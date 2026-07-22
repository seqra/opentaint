package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.access.suffix.materializeSuffixes
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.atomic.AtomicLong

/**
 * Opt-in capture of the edges that actually cross the IFDS worklist and summary boundary.
 *
 * Tests use this instead of inferring propagation shape from the final finding set. Keeping the
 * original [Edge] is intentional: suffix tests need to inspect edge-level bundles. The
 * materialized language is snapshotted while the AP manager is active, so tests can compare it
 * with Tree mode after the analyzer has closed.
 */
object FactPropagationTracer {
    enum class Kind { Propagation, Summary }

    data class Event(
        val sequence: Long,
        val kind: Kind,
        val methodEntryPoint: MethodEntryPoint,
        val edge: Edge,
        val materializedFactToFact: List<FactToFactSnapshot>,
    )

    data class FactToFactSnapshot(
        val statement: String,
        val initialBase: String,
        val finalBase: String,
        val initialFact: String,
        val finalFact: String,
    )

    @Volatile
    var enabled: Boolean = false

    private val sequence = AtomicLong()
    private val events = ConcurrentLinkedQueue<Event>()

    fun propagation(methodEntryPoint: MethodEntryPoint, edge: Edge) {
        record(Kind.Propagation, methodEntryPoint, edge)
    }

    fun summary(methodEntryPoint: MethodEntryPoint, edge: Edge) {
        record(Kind.Summary, methodEntryPoint, edge)
    }

    private fun record(kind: Kind, methodEntryPoint: MethodEntryPoint, edge: Edge) {
        if (!enabled) return
        val materialized = if (edge is Edge.FactToFact) {
            edge.materializeSuffixes().map {
                FactToFactSnapshot(
                    statement = it.statement.toString(),
                    initialBase = it.initialFactAp.base.toString(),
                    finalBase = it.factAp.base.toString(),
                    initialFact = it.initialFactAp.toString(),
                    finalFact = it.factAp.toString(),
                )
            }
        } else {
            emptyList()
        }
        events += Event(sequence.getAndIncrement(), kind, methodEntryPoint, edge, materialized)
    }

    fun snapshot(): List<Event> = events.sortedBy { it.sequence }

    fun reset() {
        events.clear()
        sequence.set(0)
    }
}
