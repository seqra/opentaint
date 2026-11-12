package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.PortId
import java.util.Collections

/** Query identity keeps the packet's protection class explicitly, as do retained Facts. */
internal data class LoopPacketKey(val facts: Facts, val protection: TaintNode? = (facts as? TaintTree)?.nonSubsumable)
private class IdentityKey(private val value: Any) {
    override fun equals(other: Any?): Boolean = other is IdentityKey && value === other.value
    override fun hashCode(): Int = System.identityHashCode(value)
}

internal class LoopQueryCounts {
    var c2Queries = 0L; var c2Hits = 0L; var c2Native = 0L; var c2Rows = 0L
    var probeUnsupported = 0L; var probeComplete = 0L; var probeCacheHits = 0L
    var plans = 0L; var planChecks = 0L; var planHits = 0L; var planFallbacks = 0L; var emptyReplays = 0L
    var oversizedPlanRequests = 0L
    var c5PreparedQueries = 0L; var c5NativeQueries = 0L; var c5ReferenceFallbacks = 0L
}

/** One synchronous owner work quantum; never retained by a frozen result. */
internal class LoopQueryScratch(private val ap: ApManager, val counts: LoopQueryCounts) {
    private data class AdmissionKey(val view: IdentityKey, val policy: IdentityKey, val packet: LoopPacketKey)
    private data class PlanKey(val view: IdentityKey, val exit: PortId?, val policy: IdentityKey,
                               val original: PremiseKey, val templates: List<Pattern>)
    private val admissions = LinkedHashMap<AdmissionKey, Set<AdmittedInitial>>()
    private val plans = LinkedHashMap<PlanKey, PreparedLocalDataPlan?>()

    /** A miss never runs C2. Only complete answers enter this cache. */
    fun peekInitials(view: ScopeDemandView, actual: Facts, policy: RestrictedInitialPolicy): Set<AdmittedInitial>? {
        ap.cancellation.checkpoint()
        val key = AdmissionKey(IdentityKey(view), IdentityKey(policy), LoopPacketKey(actual))
        return admissions[key]?.also { counts.c2Hits++ }
    }

    fun initials(view: ScopeDemandView, actual: Facts, policy: RestrictedInitialPolicy): Set<AdmittedInitial> {
        ap.cancellation.checkpoint(); counts.c2Queries++
        val key = AdmissionKey(IdentityKey(view), IdentityKey(policy), LoopPacketKey(actual))
        admissions[key]?.let { counts.c2Hits++; return it }
        counts.c2Native++
        val answer = view.initials(actual, policy)
        counts.c2Rows += answer.size
        if (answer.size > 128) return answer
        if (admissions.size == 32) admissions.clear()
        return Collections.unmodifiableSet(LinkedHashSet(answer)).also { admissions[key] = it }
    }

    fun plan(view: Any, exit: PortId?, original: PremiseKey, templates: List<Pattern>, policy: RestrictedInitialPolicy,
             prepare: () -> PreparedLocalDataPlan?): PreparedLocalDataPlan? {
        ap.cancellation.checkpoint()
        if (templates.size > 2048 || original.size > 2048) {
            counts.planFallbacks++; counts.oversizedPlanRequests++; return null
        }
        val key = PlanKey(IdentityKey(view), exit, IdentityKey(policy), original, templates)
        if (plans.containsKey(key)) { counts.planHits++; return plans[key] }
        counts.plans++
        val result = prepare()
        if (result == null) counts.planFallbacks++
        if (plans.size == 32) plans.clear()
        plans[key] = result
        return result
    }
    fun clear() { admissions.clear(); plans.clear() }
    internal val retainedAdmissionCount get() = admissions.size
    internal val retainedPlanCount get() = plans.size
}

/** Per-observation bundle also retains oversize answers for its two projections. */
internal class LoopAdmissionBundle(
    private val adjacentQuery: () -> List<LoopLabelledAdmission>,
    private val repeatQuery: () -> List<LoopLabelledAdmission>,
) {
    private val adjacent by lazy(LazyThreadSafetyMode.NONE, adjacentQuery)
    private val repeat by lazy(LazyThreadSafetyMode.NONE, repeatQuery)
    fun adjacent(): Set<AdmittedInitial> = adjacent.mapTo(LinkedHashSet()) { it.admitted }
    fun repeat(): Set<AdmittedInitial> = repeat.mapTo(LinkedHashSet()) { it.admitted }
    fun labelled(): Collection<LoopLabelledAdmission> = adjacent + repeat
    companion object {
        fun fromDescriptors(ap: ApManager, descriptors: List<LoopAdmissionDescriptor>): LoopAdmissionBundle {
            val materialized = HashMap<InitialEmission, AdmittedInitial>()
            fun selected(family: LoopAdmissionFamily): List<LoopLabelledAdmission> =
                descriptors.filter { it.family == family }.map { descriptor ->
                    val emission = InitialEmission(descriptor.pattern, descriptor.layer)
                    val initial = materialized.getOrPut(emission) {
                        AdmittedInitial(ap.initial(emission.pattern), emission.layer)
                    }
                    LoopLabelledAdmission(descriptor.scope, family, initial)
                }
            return LoopAdmissionBundle({ selected(LoopAdmissionFamily.ADJACENT) },
                { selected(LoopAdmissionFamily.REPEAT) })
        }
    }

}


internal data class LoopAdmissionDescriptor(val scope: BlockScope, val family: LoopAdmissionFamily,
                                           val pattern: Pattern, val layer: Layer)

internal data class LoopAdmissionConsumer(val scope: BlockScope, val family: LoopAdmissionFamily,
                                         val demand: ScopeDemandView, val keep: (Facts) -> Boolean)

internal sealed interface LoopAdmissionProbe {
    data class Rejected(val extra: LoopAdmissionDescriptor) : LoopAdmissionProbe
    data class Complete(val bundle: LoopAdmissionBundle) : LoopAdmissionProbe
    data object Unsupported : LoopAdmissionProbe
}

/** Negative membership witnesses reject a trial; absence of one never accepts it. */
internal fun probeLoopAdmissions(ap: ApManager, policy: RestrictedInitialPolicy, actual: Facts,
                                 expected: Set<LoopAdmissionDescriptor>, consumers: List<LoopAdmissionConsumer>,
                                 scratch: LoopQueryScratch?, counts: LoopQueryCounts): LoopAdmissionProbe {
    ap.cancellation.checkpoint()
    // Preflight the complete route set, before running any emitter or cache lookup.
    if (consumers.any { (it.demand as? LocalAdmissionView)?.supportsScan(actual, policy) != true }) {
        counts.probeUnsupported++
        return LoopAdmissionProbe.Unsupported
    }
    val complete = ArrayList<LoopAdmissionDescriptor>()
    for (consumer in consumers) {
        ap.cancellation.checkpoint()
        if (!consumer.keep(actual)) continue
        var extra: LoopAdmissionDescriptor? = null
        fun offer(emitted: InitialEmission): DemandVisit {
            ap.cancellation.checkpoint()
            val descriptor = LoopAdmissionDescriptor(consumer.scope, consumer.family, emitted.pattern, emitted.layer)
            if (descriptor !in expected) { extra = descriptor; return DemandVisit.STOP }
            complete += descriptor
            return DemandVisit.CONTINUE
        }
        counts.c2Queries++
        val cached = scratch?.peekInitials(consumer.demand, actual, policy)
        if (cached != null) {
            counts.probeCacheHits++
            for (initial in cached) if (offer(InitialEmission(initial.initial.toPattern(), initial.layer)) == DemandVisit.STOP)
                break
        } else {
            counts.c2Native++
            val status = (consumer.demand as LocalAdmissionView).visitInitialEmissions(actual, policy) {
                counts.c2Rows++
                offer(it)
            }
            check(status != DemandScan.UNSUPPORTED) { "A preflighted frozen demand view changed capability" }
            check(status != DemandScan.STOPPED || extra != null)
        }
        extra?.let { return LoopAdmissionProbe.Rejected(it) }
    }
    counts.probeComplete++
    return LoopAdmissionProbe.Complete(LoopAdmissionBundle.fromDescriptors(ap, complete))
}
