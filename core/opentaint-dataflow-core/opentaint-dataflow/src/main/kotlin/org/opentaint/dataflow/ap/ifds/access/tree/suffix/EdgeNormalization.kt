package org.opentaint.dataflow.ap.ifds.access.tree.suffix

import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree

object EdgeNormalization {
    data class NormalizedFact(
        val initialAccess: AccessPath.AccessNode?,
        val finalAccess: AccessPath.AccessNode?,
        val suffix: AccessTree.AccessNode,
    )

    fun normalizeFacts(initial: FactAccess, final: FactAccess): NormalizedFact {
        if (initial.suffix == final.suffix) {
            val normalizedAccess = normalizeAccess(initial.access, final.access)
            val normalizedSuffix = initial.suffix.prepend(normalizedAccess.commonSuffix)
            return NormalizedFact(normalizedAccess.initial, normalizedAccess.final, normalizedSuffix)
        }

        TODO()
    }

    data class NormalizedAccess(
        val initial: AccessPath.AccessNode?,
        val final: AccessPath.AccessNode?,
        val commonSuffix: AccessPath.AccessNode?,
    )

    private fun normalizeAccess(
        initial: AccessPath.AccessNode?,
        final: AccessPath.AccessNode?
    ): NormalizedAccess {
        if (initial == null || final == null) {
            return NormalizedAccess(initial, final, null)
        }

        TODO()
    }

}
