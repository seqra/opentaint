package org.opentaint.dataflow.ap.ifds.analysis.alias

interface ImmutableIntDSU {
    fun mutableCopy(): IntDisjointSets
}
