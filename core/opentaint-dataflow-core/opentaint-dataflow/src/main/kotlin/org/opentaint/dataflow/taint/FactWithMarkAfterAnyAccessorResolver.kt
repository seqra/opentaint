package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor

interface FactWithMarkAfterAnyAccessorResolver {
    fun resolve(mark: TaintMarkAccessor)
}
