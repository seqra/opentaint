package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.ExactDemandResults
import org.opentaint.dataflow.bidi.store.ScopeDemandView
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.graph.PortId

/** The router supplies a witness for the boundary which was actually reached. */
internal enum class BlockEntryRole { NORMAL_INTERFACE, EXCEPTIONAL_INTERFACE, MID_BLOCK }

internal data class BlockBoundaryAdmission(val initials: Set<AdmittedInitial>,
                                         val borrowedExceptionalNormalZero: Boolean)

/**
 * DATA keeps its exact physical interface. Typed ZERO control also sees the
 * normal endpoint when that endpoint was reached. The exceptional case below
 * is the selected HACK, rather than a new block seed or an alias of DATA rows.
 */
internal class BlockBoundaryDemandView(
    private val ap: ApManager,
    private val physical: ScopeDemandView,
    private val normal: ScopeDemandView,
    direction: Direction,
    role: BlockEntryRole,
    normalOutputs: Collection<PortId>,
    private val staticShortcutTarget: (PortId, PremiseKey, RestrictedInitialPolicy) -> Boolean = { _, _, _ -> false },
) : org.opentaint.dataflow.bidi.store.PreparedScopeDemandView, org.opentaint.dataflow.bidi.store.EntryPrecisionView {
    private val outputs = normalOutputs.toSet()
    private val exceptionalHack = direction == Direction.BACKWARD && role == BlockEntryRole.EXCEPTIONAL_INTERFACE
    private val backward = direction == Direction.BACKWARD
    private val borrowNormal = role == BlockEntryRole.NORMAL_INTERFACE ||
        exceptionalHack

    fun admission(actual: Facts, policy: RestrictedInitialPolicy): BlockBoundaryAdmission {
        val result = LinkedHashSet(physical.initials(actual, policy))
        // HACK: backward ZERO at the actual exceptional interface applies the
        // normal exit's control demands too. Ordinary DATA never reads them.
        var borrowed = false
        if (borrowNormal && actual is Reach) {
            val selected = normal.initials(actual, policy)
            result += selected
            borrowed = exceptionalHack && selected.any { it.initial.isZero }
        }
        return BlockBoundaryAdmission(result, borrowed)
    }

    override fun initials(actual: Facts, policy: RestrictedInitialPolicy): Set<AdmittedInitial> =
        admission(actual, policy).initials

    override fun precisionCursors(actual: Pattern, policy: RestrictedInitialPolicy): List<org.opentaint.dataflow.bidi.store.AnyDemandCursor>? =
        (physical as? org.opentaint.dataflow.bidi.store.EntryPrecisionView)?.precisionCursors(actual, policy)

    override fun prepareDataPlan(exit: PortId, templates: List<Pattern>,
                                 policy: RestrictedInitialPolicy, onEntryCheck: () -> Unit): org.opentaint.dataflow.bidi.store.PreparedLocalDataPlan? =
        (physical as? org.opentaint.dataflow.bidi.store.PreparedScopeDemandView)?.prepareDataPlan(exit, templates, policy, onEntryCheck)

    override fun intersect(exit: PortId, original: PremiseKey, raw: Facts,
                           policy: RestrictedInitialPolicy): List<Facts> {
        val result = ExactDemandResults(ap)
        physical.intersect(exit, original, raw, policy).forEach(result::add)
        if (borrowNormal && original.isZero)
            normal.intersect(exit, original, raw, policy).forEach(result::add)
        return result.all()
    }

    override fun acceptsTarget(exit: PortId, original: PremiseKey,
                               policy: RestrictedInitialPolicy): Boolean {
        // A Target is attached to the normal interface. A matching complete
        // paired row can name any genuine normal physical output of this block.
        for (output in outputs + exit) {
            ap.cancellation.checkpoint()
            if (physical.acceptsTarget(output, original, policy)) return true
            if (borrowNormal && original.isZero && normal.acceptsTarget(output, original, policy)) return true
            // The write shortcut has its own exact paired completion row.
            // It is not a DATA admission alias of the normal control view.
            if (backward && policy.run == 2 && original is InitialAp && original.base == STATIC &&
                staticShortcutTarget(output, original, policy)) return true
        }
        return false
    }
}

/** Only handoff control metadata uses the borrowed normal invocation address.
 * A synthetic discovery ingress is not a forward DATA/native output port. */
internal fun targetHandoffScope(actual: BlockScope, direction: Direction, borrowedNormalZero: Boolean,
                                row: TargetSummary): BlockScope =
    if (direction == Direction.BACKWARD && borrowedNormalZero && row.premise.isZero && row.target == Target.DemandTarget)
        actual.copy(entry = PortId.ROOT_EXIT) else actual
