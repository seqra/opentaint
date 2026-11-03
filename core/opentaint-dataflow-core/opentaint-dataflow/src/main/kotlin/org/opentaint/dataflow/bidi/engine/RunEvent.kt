package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.Facts
import org.opentaint.dataflow.bidi.ap.AdmittedInitial
import org.opentaint.dataflow.bidi.ap.Layer
import org.opentaint.dataflow.bidi.ap.MethodKey
import org.opentaint.dataflow.bidi.store.CallerRef
import org.opentaint.dataflow.bidi.store.BlockScope
import java.util.Collections

sealed interface RunEvent {
    data class Start(val root: MethodKey) : RunEvent
    data class LinkIn(val callee: MethodKey, val ref: CallerRef, val linkLayer: Layer, val added: Facts) : RunEvent
    /** Restricted callers have already completed demand lookup and initial emission. */
    class InitialsIn(val callee: MethodKey, initials: Collection<AdmittedInitial>) : RunEvent {
        val initials: List<AdmittedInitial> = Collections.unmodifiableList(ArrayList(initials))
        init { require(this.initials.isNotEmpty()) }
    }
    data class StaticOwner(val effect: StaticOwnerEffect) : RunEvent

    /** A detached immutable batch addressed to the method's actual block entry. */
    data class MarkRequestsIn(val method: MethodKey, val rows: RequestRows,
                              val scope: BlockScope = BlockScope.ROOT) : RunEvent

    /** Only a subscribed caller runner handles this event; the publisher reads no caller directory. */
    data class ChangedRequests(val callee: MethodKey, val rows: RequestRows) : RunEvent

    /** Answers own only initial keys and layers, never supplier Facts or caller bindings. */
    class InitialAnswersIn(val method: MethodKey, answers: Collection<AdmittedInitial>) : RunEvent {
        val answers: List<AdmittedInitial> = Collections.unmodifiableList(ArrayList(answers))
    }

    /** The publisher can clear its pending list as soon as this event is sent. */
    class Delivery(val callee: MethodKey, publications: List<Publication>) : RunEvent {
        val publications: List<Publication> = Collections.unmodifiableList(ArrayList(publications))
    }

    class TargetDelivery(val callee: MethodKey, rows: TargetBatch) : RunEvent {
        val rows: TargetBatch = Collections.unmodifiableList(ArrayList(rows))
    }

    class Work(val analyzer: RunActor) : RunEvent
}

fun RunEvent.target(): MethodKey = when (this) {
    is RunEvent.Start -> root
    is RunEvent.LinkIn -> callee
    is RunEvent.InitialsIn -> callee
    is RunEvent.StaticOwner -> effect.owner
    is RunEvent.MarkRequestsIn -> method
    is RunEvent.InitialAnswersIn -> method
    is RunEvent.Delivery, is RunEvent.TargetDelivery, is RunEvent.ChangedRequests, is RunEvent.Work ->
        error("Delivery and Work require their owning runner")
}
