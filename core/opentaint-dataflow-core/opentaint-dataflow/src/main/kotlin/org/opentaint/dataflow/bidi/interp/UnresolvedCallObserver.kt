package org.opentaint.dataflow.bidi.interp

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.ir.api.common.cfg.CommonCallExpr

/** Run 1 reports each new TAINT delta at an unresolved stage. This hook does not select facts. */
fun interface UnresolvedCallObserver {
    fun reached(call: CommonCallExpr, position: AccessPathBase, plan: CallPlan)
}

/** Optional immutable capability. Keep the observer itself a Java/Kotlin SAM. */
interface UnresolvedCallObserverState {
    val enabled: Boolean
}

/** Existing observers remain enabled unless they explicitly opt out. */
val UnresolvedCallObserver.enabled: Boolean
    get() = (this as? UnresolvedCallObserverState)?.enabled ?: true
