package org.opentaint.dataflow.ap.ifds.access.common

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactList
import org.opentaint.dataflow.ap.ifds.access.FactDemandState

abstract class CommonFinalFactList<FAP> : FinalFactList, FinalApAccess<FAP> {
    abstract val storage: AccessStorage<FAP>

    interface AccessStorage<FAP> {
        fun add(fact: FAP)
        fun get(idx: Int): FAP
        fun removeLast(): FAP
    }

    class Default<FAP> : AccessStorage<FAP> {
        private val storage = mutableListOf<FAP>()
        override fun add(fact: FAP) {
            storage.add(fact)
        }

        override fun get(idx: Int): FAP = storage[idx]
        override fun removeLast(): FAP = storage.removeLast()
    }

    private val bases = mutableListOf<AccessPathBase>()
    private val demandStates = mutableListOf<FactDemandState>()

    override fun add(fact: FinalFactAp) {
        bases.add(fact.base)
        demandStates.add(fact.demandState)
        storage.add(getFinalAccess(fact))
    }

    override operator fun get(idx: Int): FinalFactAp =
        createFinal(bases[idx], storage.get(idx), demandStates[idx])

    override fun removeLast(): FinalFactAp =
        createFinal(bases.removeLast(), storage.removeLast(), demandStates.removeLast())
}
