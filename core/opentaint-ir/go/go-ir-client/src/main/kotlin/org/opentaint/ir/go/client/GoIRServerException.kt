package org.opentaint.ir.go.client

/**
 * Raised when the go-ssa-server RPC fails at the transport level (for example
 * `UNAVAILABLE: Network closed for unknown reason`, which is what gRPC reports
 * when the server process dies mid-stream).
 *
 * The [message] is enriched with server-process diagnostics (exit state and the
 * captured stderr tail) so failures — especially on CI, where the process can't
 * be inspected interactively — explain the underlying crash. The original gRPC
 * exception is preserved as the [cause].
 */
class GoIRServerException(message: String, cause: Throwable) : RuntimeException(message, cause)
