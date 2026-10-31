package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.interp.MicroEdge

/** The executable BIDI domain excludes literal-backed data. IR effects and
 * generic AP templates still describe literals, including overwrite kills. */
object RuntimeDataDomain {
    fun base(base: AccessPathBase): Boolean = base !is AccessPathBase.Constant
    fun initial(initial: InitialAp): Boolean = base(initial.base)
    fun premise(premise: PremiseKey): Boolean {
        for (member in 0 until premise.size) if (!initial(premise.member(member))) return false
        return true
    }
    fun packet(premise: PremiseKey, facts: Facts): Boolean = premise(premise) && base(facts.base)
    fun producer(edge: PathEdge): Boolean = base(edge.from.base) && base(edge.to.base)
    fun producer(edge: MicroEdge): Boolean = producer(edge.edge) && producer(edge.forward)
}
