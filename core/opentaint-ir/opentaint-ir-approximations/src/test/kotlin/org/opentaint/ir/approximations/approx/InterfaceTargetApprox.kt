package org.opentaint.ir.approximations.approx

import org.opentaint.ir.approximation.annotation.Approximate
import org.opentaint.ir.approximations.target.InterfaceTarget

@Approximate(InterfaceTarget::class)
class InterfaceTargetApprox {
    private var approximationState: String? = null

    fun convert(value: String): String {
        approximationState = value
        return approximationState!!
    }

    fun approximationHelper(value: String): String = value
}
