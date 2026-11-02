package org.opentaint.ir.go.impl

import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRModelFunction

/**
 * Function identity shared by every [GoIRFunction] implementation in this module.
 * A model keeps the name of the function it replaces, so model-ness is part of the identity:
 * otherwise bodies and instruction locations of a model and its original would compare equal.
 */
internal fun GoIRFunction.functionEquals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is GoIRFunction) return false
    return fullName == other.fullName && (this is GoIRModelFunction) == (other is GoIRModelFunction)
}

internal fun GoIRFunction.functionHashCode(): Int =
    31 * fullName.hashCode() + if (this is GoIRModelFunction) 1 else 0
