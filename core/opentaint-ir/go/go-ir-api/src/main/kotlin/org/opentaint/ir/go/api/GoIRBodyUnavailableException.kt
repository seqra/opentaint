package org.opentaint.ir.go.api

class GoIRBodyUnavailableException(val functionFullName: String) : RuntimeException(
    "Function body for '$functionFullName' is not loaded: it belongs to a dependency or stdlib package loaded in PROJECT mode, or the function has no SSA body",
)
