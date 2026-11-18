package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.AdmittedInitial
import org.opentaint.dataflow.bidi.ap.Facts
import org.opentaint.dataflow.bidi.ap.InitialAp
import org.opentaint.dataflow.bidi.ap.Pattern
import org.opentaint.dataflow.bidi.ap.PremiseKey
import org.opentaint.dataflow.graph.PortId

/** Control endpoints do not have an access path and must not enter an AP trie. */
sealed interface DemandEntry {
    data class Data(val pattern: Pattern) : DemandEntry
    data object Zero : DemandEntry
    data object Target : DemandEntry
}

sealed interface DemandExit {
    data class Data(val pattern: Pattern) : DemandExit
    data object Zero : DemandExit
}

data class PairedDemand(val entry: DemandEntry, val exit: DemandExit)

/** Row and raw query within the enclosing method/block entry. A virtual C2
 * lookup witnesses only the entry projection; C5 must still select a whole row. */
data class DemandQualification(
    val row: PairedDemand?,
    val rawInitial: InitialAp,
    val exit: PortId? = null,
    val virtualEntry: DemandEntry? = null,
) {
    fun matches(binding: DemandQualification?): Boolean {
        if (binding == null || rawInitial !== binding.rawInitial) return false
        if (binding.row != null)
            return row == binding.row && exit == binding.exit && virtualEntry == binding.virtualEntry
        return row != null && virtualEntry != null && virtualEntry == binding.virtualEntry &&
            (binding.exit == null || binding.exit == exit)
    }
}

/** A command and the specific offered leaf that authorized its continuation. */
data class BoundAdmission(
    val admitted: AdmittedInitial, val qualification: DemandQualification?, val actual: Pattern, val possible: Boolean,
)

data class AdmittedSummary(
    val premise: PremiseKey, val facts: Facts, val qualification: DemandQualification? = null,
)
