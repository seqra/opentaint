package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.*

/** Initial keys are manager-interned and have identity equality. */
class InitialFactStore {
    private val initials = LinkedHashMap<InitialAp, Int>()

    fun add(seed: AdmittedInitial): Boolean {
        if (!RuntimeDataDomain.initial(seed.initial)) return false
        val canonical = canonicalAdmission(seed.initial, seed.layer)
        val bit = 1 shl canonical.layer.ordinal
        val old = initials[canonical.initial] ?: 0
        if (old and bit != 0) return false
        initials[canonical.initial] = old or bit
        return true
    }

    /** Explicit legacy entry: use the intrinsic start policy, with no actual-input support. */
    fun add(i: InitialAp): Boolean = add(AdmittedInitial(i, Layer.NORMAL))

    fun all(): Collection<InitialAp> = initials.keys.toList()
    fun admissions(): Collection<AdmittedInitial> = initials.flatMap { (initial, mask) ->
        Layer.entries.filter { mask and (1 shl it.ordinal) != 0 }.map { AdmittedInitial(initial, it) }
    }
}
