package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.Pattern

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
