package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.MethodKey
import org.opentaint.dataflow.bidi.ap.PremiseKey

@JvmInline value class ReportId(val value: Int)

/** Terminal observations have no AP geometry and never become method facts. */
sealed interface Target {
    data class NormalTarget(val id: ReportId) : Target
    data object DemandTarget : Target
}

data class TargetSummary(val premise: PremiseKey, val target: Target)
data class OwnedNormalTarget(val method: MethodKey, val premise: PremiseKey, val id: ReportId)
typealias TargetBatch = List<TargetSummary>

/** The existing static continuation can carry an AP image or a terminal result. */
sealed interface StaticCallResult {
    data class Ap(val publication: Publication) : StaticCallResult
    data class Terminal(val summary: TargetSummary) : StaticCallResult
    val premise: PremiseKey get() = when (this) {
        is Ap -> publication.premise
        is Terminal -> summary.premise
    }
}

fun interface TargetPublicationSink {
    fun publishTargets(method: MethodKey, batch: TargetBatch)
}

interface TargetApplier {
    fun applyTarget(part: Subscription, row: TargetSummary, member: Int) {
        error("This summary applier does not support terminal results")
    }
    fun applyStaticTarget(part: Subscription, row: TargetSummary, member: Int) {
        error("This summary applier does not support static terminal results")
    }
}
