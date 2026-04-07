package org.opentaint.dataflow.ap.ifds.access.typed

import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAbstraction
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp

interface TypedInitialFactAbstraction<IF : InitialFactAp, FF : FinalFactAp> : InitialFactAbstraction {
    override fun addAbstractedInitialFact(
        factAp: FinalFactAp,
        typeChecker: FactTypeChecker
    ): List<Pair<InitialFactAp, FinalFactAp>> =
        @Suppress("UNCHECKED_CAST")
        typedAddAbstractedInitialFact(factAp as FF, typeChecker)

    override fun registerNewInitialFact(
        factAp: InitialFactAp,
        typeChecker: FactTypeChecker
    ): List<Pair<InitialFactAp, FinalFactAp>> =
        @Suppress("UNCHECKED_CAST")
        typedRegisterNewInitialFact(factAp as IF, typeChecker)

    fun typedAddAbstractedInitialFact(
        factAp: FF,
        typeChecker: FactTypeChecker
    ): List<Pair<IF, FF>>

    fun typedRegisterNewInitialFact(
        factAp: IF,
        typeChecker: FactTypeChecker
    ): List<Pair<IF, FF>>
}
