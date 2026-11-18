package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.BoundAdmission

internal fun TargetSummary.hasPossibleInput(initial: InitialAp, admissions: Set<BoundAdmission>): Boolean {
    val qualified = qualification ?: return false
    return target == Target.DemandTarget && qualified.rawInitial === initial &&
        admissions.any { it.possible && qualified.matches(it.qualification) }
}

/** Build an application-local operand for an admitted possible binding. */
internal fun possibleSummaryInputs(
    ap: ApManager, original: Facts, row: Publication, member: Int, admissions: Set<BoundAdmission>,
): Sequence<Facts> = sequence {
    val qualification = row.qualification ?: return@sequence
    val initial = row.premise.member(member)
    val raw = qualification.rawInitial
    if (initial.base != raw.base || initial.path != raw.path || initial.mark != raw.mark) return@sequence
    for (admission in admissions) {
        ap.cancellation.checkpoint()
        if (!admission.possible || !qualification.matches(admission.qualification)) continue
        val actual = admission.actual.fact
        val selected = ap.factsOf(actual.copy(path = raw.pathData.asList(),
            tail = if (raw.tail == Tail.EXACT) Tail.EXACT else Tail.ANY), ExclusionSet.Empty, Layer.DEMAND)
        if (original !is TaintTree || selected !is TaintTree) {
            yield(selected)
            continue
        }
        val mark = (actual.mark as MarkSlot.Concrete).mark
        var protection = original.nonSubsumable
        for (field in actual.path) protection = protection?.child(field)
        val protected = protection?.leaf?.let { mark in if (actual.tail == Tail.EXACT) it.exact else it.any } == true
        yield(if (protected) selected.withProtection(selected.root, ap.cancellation) else selected)
    }
}
