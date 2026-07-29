package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyFieldMarkExclusions
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner

/** Converts Cactus mark objects to the indices used by [AnyFieldMarkExclusions]. */
internal object CactusMarkInterner {
    private val accessors = AccessorInterner()

    fun index(mark: TaintMarkAccessor): AccessorIdx = accessors.index(mark)

    fun mark(index: AccessorIdx): TaintMarkAccessor =
        accessors.accessor(index) as? TaintMarkAccessor
            ?: error("Cactus AnyField exclusion is not a taint mark: $index")
}
