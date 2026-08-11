package org.opentaint.ir.api.common.cfg

import org.opentaint.ir.api.common.CommonMethod

interface CommonInst {
    val location: CommonInstLocation
}

interface CommonInstLocation {
    val method: CommonMethod

    /** Position of the instruction inside its method body: a JVM-object-free coordinate
     * for stable ordering (see trace/path/Source2SinkTraceGraph.kt). */
    val index: Int
}

interface CommonAssignInst : CommonInst {
    val lhv: CommonValue
    val rhv: CommonExpr
}

interface CommonCallInst : CommonInst

interface CommonReturnInst : CommonInst {
    val returnValue: CommonValue?
}

interface CommonGotoInst : CommonInst

interface CommonIfInst : CommonInst
