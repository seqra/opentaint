package org.opentaint.dataflow.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.taint.FinalFactReader

interface MethodCallFlowFunction {
    sealed interface CallFact

    sealed interface Call2ReturnFact

    sealed interface ZeroCallFact: CallFact

    sealed interface FactCallFact: CallFact

    sealed interface NDFactCallFact: CallFact

    sealed interface ZeroCallFailureFact: ZeroCallFact

    sealed interface FactCallFailureFact: FactCallFact

    sealed interface NDFactCallFailureFact: NDFactCallFact

    data object Unchanged : ZeroCallFact, FactCallFact, NDFactCallFact

    data object CallToReturnZeroFact: ZeroCallFact, Call2ReturnFact, ZeroCallFailureFact

    data object CallToStartZeroFact : ZeroCallFact

    data class CallToReturnFFact(
        val initialFactAp: InitialFactAp,
        val factAp: FinalFactAp,
        val traceInfo: TraceInfo?,
    ) : FactCallFact, ZeroCallFact, Call2ReturnFact, FactCallFailureFact, ZeroCallFailureFact

    data class CallToStartFFact(
        val initialFactAp: InitialFactAp,
        val callerFactAp: FinalFactAp,
        val startFactBase: AccessPathBase,
        val traceInfo: TraceInfo?,
    ) : FactCallFact

    data class CallToReturnZFact(
        val factAp: FinalFactAp,
        val traceInfo: TraceInfo?,
    ) : ZeroCallFact, FactCallFact, NDFactCallFact, Call2ReturnFact, ZeroCallFailureFact, FactCallFailureFact, NDFactCallFailureFact

    data class CallToStartZFact(
        val callerFactAp: FinalFactAp,
        val startFactBase: AccessPathBase,
        val traceInfo: TraceInfo?,
    ) : ZeroCallFact

    data class CallToReturnNonDistributiveFact(
        val initialFacts: Set<InitialFactAp>,
        val factAp: FinalFactAp,
        val traceInfo: TraceInfo?,
    ) : FactCallFact, ZeroCallFact, NDFactCallFact, Call2ReturnFact, FactCallFailureFact, ZeroCallFailureFact, NDFactCallFailureFact

    data class CallToStartNDFFact(
        val initialFacts: Set<InitialFactAp>,
        val callerFactAp: FinalFactAp,
        val startFactBase: AccessPathBase,
        val traceInfo: TraceInfo?,
    ) : NDFactCallFact

    data class SideEffectRequirement(val initialFactAp: InitialFactAp) : FactCallFact, FactCallFailureFact

    data class ZeroSideEffect(val kind: SideEffectKind) : ZeroCallFact, ZeroCallFailureFact
    data class FactSideEffect(val initialFactAp: InitialFactAp, val kind: SideEffectKind) : FactCallFact, FactCallFailureFact

    data class Drop(
        val traceInfo: TraceInfo?,
    ) : ZeroCallFact, FactCallFact, NDFactCallFact, Call2ReturnFact

    sealed interface TraceInfo {
        data object Flow : TraceInfo
        data class Rule(val rule: CommonTaintConfigurationItem, val action: CommonTaintAction): TraceInfo
    }

    fun propagateZeroToZero(): Set<ZeroCallFact>
    fun propagateZeroToFact(currentFactAp: FinalFactAp): Set<ZeroCallFact>
    fun propagateFactToFact(initialFactAp: InitialFactAp, currentFactAp: FinalFactAp): Set<FactCallFact>
    fun propagateNDFactToFact(initialFacts: Set<InitialFactAp>, currentFactAp: FinalFactAp): Set<NDFactCallFact>

    fun propagateZeroToZeroResolutionFailure(): Set<ZeroCallFailureFact>
    fun propagateZeroToFactResolutionFailure(currentFactAp: FinalFactAp, startFactBase: AccessPathBase): Set<ZeroCallFailureFact>
    fun propagateFactToFactResolutionFailure(initialFactAp: InitialFactAp, currentFactAp: FinalFactAp, startFactBase: AccessPathBase): Set<FactCallFailureFact>
    fun propagateNDFactToFactResolutionFailure(initialFacts: Set<InitialFactAp>, currentFactAp: FinalFactAp, startFactBase: AccessPathBase): Set<NDFactCallFailureFact>

    interface Default : MethodCallFlowFunction {
        override fun propagateZeroToFact(currentFactAp: FinalFactAp) = buildSet {
            propagateFact(
                initialFacts = emptySet(),
                exclusion = ExclusionSet.Universe,
                factAp = currentFactAp,
                skipCall = { this += Unchanged },
                addSideEffectRequirement = { factReader ->
                    check(!factReader.hasRefinement) { "Can't refine Zero fact" }
                },
                addCallToReturn = { factReader, factAp, trace ->
                    check(!factReader.hasRefinement) { "Can't refine Zero fact" }
                    this += CallToReturnZFact(factAp, trace)
                },
                addCallToStart = { factReader, callerFactAp, startFactBase, trace ->
                    check(!factReader.hasRefinement) { "Can't refine Zero fact" }
                    this += CallToStartZFact(callerFactAp, startFactBase, trace)
                },
                addUnchecked = {
                    check(it is ZeroCallFact) { "unexpected" }
                    this += it
                },
            )
        }

        override fun propagateFactToFact(
            initialFactAp: InitialFactAp,
            currentFactAp: FinalFactAp
        ) = buildSet {
            propagateFact(
                initialFacts = setOf(initialFactAp),
                exclusion = initialFactAp.exclusions,
                factAp = currentFactAp,
                skipCall = { this += Unchanged },
                addSideEffectRequirement = { factReader ->
                    this += SideEffectRequirement(factReader.refineFact(initialFactAp.replaceExclusions(ExclusionSet.Empty)))
                },
                addCallToReturn = { factReader, factAp, trace ->
                    this += CallToReturnFFact(
                        factReader.refineFact(initialFactAp),
                        factReader.refineFact(factAp),
                        trace
                    )
                },
                addCallToStart = { factReader, callerFactAp, startFactBase, trace ->
                    this += CallToStartFFact(
                        factReader.refineFact(initialFactAp),
                        factReader.refineFact(callerFactAp),
                        startFactBase, trace
                    )
                },
                addUnchecked = {
                    check(it is FactCallFact) { "unexpected" }
                    this += it
                },
            )
        }

        override fun propagateNDFactToFact(
            initialFacts: Set<InitialFactAp>,
            currentFactAp: FinalFactAp
        ): Set<NDFactCallFact> = buildSet {
            propagateFact(
                initialFacts = initialFacts,
                exclusion = ExclusionSet.Universe,
                factAp = currentFactAp,
                skipCall = { this += Unchanged },
                addSideEffectRequirement = { factReader ->
                    check(!factReader.hasRefinement) { "Can't refine NDF2F edge" }
                },
                addCallToReturn = { factReader, factAp, trace ->
                    check(!factReader.hasRefinement) { "Can't refine NDF2F edge" }
                    this += CallToReturnNonDistributiveFact(initialFacts, factAp, trace)
                },
                addCallToStart = { factReader, callerFactAp, startFactBase, trace ->
                    check(!factReader.hasRefinement) { "Can't refine NDF2F edge" }
                    this += CallToStartNDFFact(
                        initialFacts, callerFactAp,
                        startFactBase, trace
                    )
                },
                addUnchecked = {
                    check(it is NDFactCallFact) { "unexpected" }
                    this += it
                },
            )
        }

        override fun propagateZeroToZeroResolutionFailure(): Set<ZeroCallFailureFact> =
            setOf(CallToReturnZeroFact)

        override fun propagateZeroToFactResolutionFailure(currentFactAp: FinalFactAp, startFactBase: AccessPathBase) = buildSet {
            propagateUnresolvedCallFact(
                factAp = currentFactAp,
                addSideEffectRequirement = { factReader ->
                    check(!factReader.hasRefinement) { "Can't refine Zero fact" }
                },
                addCallToReturn = { factReader, factAp, trace ->
                    check(!factReader.hasRefinement) { "Can't refine Zero fact" }
                    this += CallToReturnZFact(factAp, trace)
                },
            )
        }

        override fun propagateFactToFactResolutionFailure(
            initialFactAp: InitialFactAp,
            currentFactAp: FinalFactAp,
            startFactBase: AccessPathBase
        ): Set<FactCallFailureFact> = buildSet {
            propagateUnresolvedCallFact(
                factAp = currentFactAp,
                addSideEffectRequirement = { factReader ->
                    this += SideEffectRequirement(factReader.refineFact(initialFactAp.replaceExclusions(ExclusionSet.Empty)))
                },
                addCallToReturn = { factReader, factAp, trace ->
                    this += CallToReturnFFact(
                        factReader.refineFact(initialFactAp),
                        factReader.refineFact(factAp),
                        trace
                    )
                },
            )
        }

        override fun propagateNDFactToFactResolutionFailure(
            initialFacts: Set<InitialFactAp>,
            currentFactAp: FinalFactAp,
            startFactBase: AccessPathBase
        ) = buildSet {
            propagateUnresolvedCallFact(
                factAp = currentFactAp,
                addSideEffectRequirement = { factReader ->
                    check(!factReader.hasRefinement) { "Can't refine NDF2F edge" }
                },
                addCallToReturn = { factReader, factAp, trace ->
                    check(!factReader.hasRefinement) { "Can't refine NDF2F edge" }
                    this += CallToReturnNonDistributiveFact(initialFacts, factAp, trace)
                },
            )
        }

        fun propagateFact(
            initialFacts: Set<InitialFactAp>,
            exclusion: ExclusionSet,
            factAp: FinalFactAp,
            skipCall: () -> Unit,
            addSideEffectRequirement: (FinalFactReader) -> Unit,
            addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo) -> Unit,
            addCallToStart: (factReader: FinalFactReader, callerFact: FinalFactAp, startFactBase: AccessPathBase, TraceInfo) -> Unit,
            addUnchecked: (CallFact) -> Unit,
        )

        fun propagateUnresolvedCallFact(
            factAp: FinalFactAp,
            addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo?) -> Unit,
            addSideEffectRequirement: (FinalFactReader) -> Unit,
        )
    }
}
