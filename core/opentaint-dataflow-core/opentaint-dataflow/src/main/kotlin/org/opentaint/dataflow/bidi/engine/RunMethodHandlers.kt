package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.MethodKey

/** Actual method actors use the run's storage and its required local and call services. */
class RunMethodHandlers(
    private val localFactory: MethodLocalServicesFactory,
    private val callFactory: MethodCallServicesFactory,
) : RunnerHandlerFactory<RunMethodAnalyzer> {
    override fun create(port: RunnerPort<RunMethodAnalyzer>): RunnerHandler<RunMethodAnalyzer> =
        Handler(port, localFactory, callFactory)

    private class Handler(
        port: RunnerPort<RunMethodAnalyzer>,
        private val localFactory: MethodLocalServicesFactory,
        private val callFactory: MethodCallServicesFactory,
    ) : RunnerHandler<RunMethodAnalyzer>, SubscriptionHandler {
        private var runner: RunnerPort<RunMethodAnalyzer>? = port
        private fun active(): RunnerPort<RunMethodAnalyzer> =
            checkNotNull(runner) { "The method handler was released" }.also {
                it.shared.cancellation.checkpoint()
            }
        private var subscriptions: SubscriptionManager? = SubscriptionManager(object : SubscriptionPort {
            override val config get() = active().config
            override val ops get() = active().ops
            override val steps get() = active().steps
            override val statistics get() = active().shared.n2Statistics
            override val abstractionStatistics get() = active().shared.abstractionStatistics
            override val requestBatchStatistics get() = active().shared.requestBatchStatistics
            override val staticService get() = active().staticService
            override fun summaryStorage(key: MethodKey): SummaryStorage = active().summaryStorage(key)
            override fun applier(key: MethodKey): SummaryApplier = active().analyzer(key)
            override fun post(event: RunEvent.TargetDelivery): Boolean = active().post(event)
            override fun post(event: RunEvent.Delivery): Boolean = active().post(event)
            override fun post(event: RunEvent.ChangedRequests): Boolean = active().post(event)
            override fun send(event: RunEvent): Boolean = active().send(event)

        })

        override fun createActor(key: MethodKey): RunMethodAnalyzer {
            val port = active()
            return RunMethodAnalyzer(key, port,
                PublicationSink { method, batch -> active().summaryStorage(method).publish(batch) },
                localFactory, callFactory,
                targetPublisher = TargetPublicationSink { method, batch -> active().summaryStorage(method).publishTargets(batch) })
        }

        override fun handle(event: RunEvent) {
            val port = active()
            when (event) {
                is RunEvent.Start -> {
                    val initials = if (port.config.run1) listOf(org.opentaint.dataflow.bidi.ap.AdmittedInitial(
                        port.shared.ap.zero, org.opentaint.dataflow.bidi.ap.Layer.NORMAL))
                        else emitRestrictedInitials(port.config, port.ops, event.root,
                            org.opentaint.dataflow.bidi.ap.Reach.NORMAL)
                    if (initials.isEmpty()) return
                    val actor = port.analyzer(event.root)
                    for (initial in initials) actor.addInitial(initial)
                }
                is RunEvent.LinkIn -> if (org.opentaint.dataflow.bidi.ap.RuntimeDataDomain.packet(event.ref.premise, event.added))
                    port.analyzer(event.callee).addLink(event.ref, event.linkLayer, event.added)
                is RunEvent.InitialsIn -> {
                    check(port.config.restricted) { "Completed initial delivery is for restricted runs" }
                    val valid = event.initials.filter { org.opentaint.dataflow.bidi.ap.RuntimeDataDomain.initial(it.initial) }
                    if (valid.isEmpty()) return
                    val actor = port.analyzer(event.callee)
                    for (initial in valid) {
                        port.shared.cancellation.checkpoint()
                        actor.addInitial(initial)
                    }
                }
                is RunEvent.StaticOwner -> port.analyzer(event.effect.owner).onStaticEffect(event.effect)
                is RunEvent.MarkRequestsIn -> {
                    val valid = event.rows.filterKeys { org.opentaint.dataflow.bidi.ap.RuntimeDataDomain.base(it.base) }
                    if (valid.isNotEmpty()) port.analyzer(event.method).addMarkRequests(valid)
                }
                is RunEvent.InitialAnswersIn -> for (initial in event.answers) {
                    port.shared.cancellation.checkpoint()
                    if (org.opentaint.dataflow.bidi.ap.RuntimeDataDomain.initial(initial.initial))
                        port.analyzer(event.method).addInitial(initial)
                }
                is RunEvent.TargetDelivery -> checkNotNull(subscriptions).onTargetDelivery(event.callee, event.rows)
                is RunEvent.Delivery -> checkNotNull(subscriptions).onDelivery(event.callee, event.publications)
                is RunEvent.ChangedRequests -> checkNotNull(subscriptions).onRequests(event.callee, event.rows)
                is RunEvent.Work -> error("Work is handled by its owning unit runner")
            }
        }

        override fun subscribe(sub: Subscription) {
            active()
            checkNotNull(subscriptions).subscribe(sub)
        }

        override fun freeze() {
            subscriptions?.freeze()
            subscriptions = null
            runner = null
        }
    }
}
