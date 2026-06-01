package org.opentaint.dataflow.go

import org.opentaint.dataflow.util.TrackerWithSubscriber
import org.opentaint.ir.go.api.GoIRFunction

object GoClosureTracker {
    class ClosureTracker : TrackerWithSubscriber<Unit, GoIRFunction, ClosureSubscriber>(Unit)
    interface ClosureSubscriber : TrackerWithSubscriber.Subscriber<Unit, GoIRFunction>
}
