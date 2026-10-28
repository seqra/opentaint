package org.opentaint.ir.go.client

import org.opentaint.ir.go.api.*
import org.opentaint.ir.go.type.*

/** Symbol resolution policy applied while a body is decoded, independent of wire decoding. */
open class GoIRBodyContext {
    open fun type(type: GoIRType): GoIRType = type
    open fun function(reference: GoIrFunctionReference): GoIrFunctionReference = reference
    open fun global(reference: GoIRGlobalReference): GoIRGlobalReference = reference
    open fun fieldIndex(type: GoIRType, index: Int, name: String): Int = index
}
