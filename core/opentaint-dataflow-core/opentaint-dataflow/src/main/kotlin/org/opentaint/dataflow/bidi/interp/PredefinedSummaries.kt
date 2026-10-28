package org.opentaint.dataflow.bidi.interp

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.bidi.ap.ApManager
import org.opentaint.ir.api.common.CommonMethod

/** A model is complete. A missing row kills that input; it does not select a fallback. */
class CompleteMethodSummary(
    normal: List<SummarySchema>,
    exceptional: List<SummarySchema> = emptyList(),
    touched: Set<AccessPathBase>,
) {
    init { require(exceptional.isEmpty()) { "Predefined exceptional rows have no supported call lane" } }
    val normal: List<SummarySchema> = ownedList(normal)
    val exceptional: List<SummarySchema> = ownedList(exceptional)
    val touched: Set<AccessPathBase> = ownedSet(touched)
    val zeroCanReturn: Boolean get() = SummarySchema.ZeroIdentity in normal

    /** The supported relations are partial identities in both directions. */
    fun reversed(): CompleteMethodSummary = this
}

sealed interface SummarySchema {
    data object ZeroIdentity : SummarySchema

    class PrefixFlowIdentity(val base: AccessPathBase, prefix: List<Accessor>) : SummarySchema {
        val prefix: List<Accessor> = ownedList(prefix)
        init { require(base != AccessPathBase.Zero) }
    }
}

/** Metadata belongs to the actual registered method and does not change its equality. */
interface PredefinedSummaryMethod {
    val predefinedSummary: CompleteMethodSummary?
}

fun predefinedSummary(method: CommonMethod): CompleteMethodSummary? =
    (method as? PredefinedSummaryMethod)?.predefinedSummary

/** This is an executable relation. It creates no method initial or inferred summary. */
fun CompleteMethodSummary.compile(manager: ApManager): StatementSummary = MicroEdgeBuilder().apply {
    for (schema in normal) when (schema) {
        SummarySchema.ZeroIdentity -> keepZero()
        is SummarySchema.PrefixFlowIdentity -> edge(keepEdge(schema.base, schema.prefix.map(manager.accessors::index)))
    }
}.buildStage()
