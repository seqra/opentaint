package org.opentaint.dataflow.taint

import org.opentaint.ir.api.common.CommonType

interface PositionTypeResolver {
    fun resolve(position: PositionAccess): CommonType?
}
