package org.opentaint.ir.impl.python

import com.google.protobuf.Message
import io.grpc.CallOptions
import io.grpc.Channel
import io.grpc.ClientCall
import io.grpc.ClientInterceptor
import io.grpc.ManagedChannel
import io.grpc.ManagedChannelBuilder
import io.grpc.MethodDescriptor
import io.grpc.protobuf.ProtoUtils

/**
 * Builds the gRPC channel to the PIR server, replacing every method's response marshaller
 * with one that parses at [PROTO_RECURSION_LIMIT] nesting levels instead of protobuf's
 * default 100.
 */
object PIRChannelFactory {

    private const val PROTO_RECURSION_LIMIT = 1000

    private const val MAX_INBOUND_MESSAGE_SIZE = 256 * 1024 * 1024

    fun forPort(port: Int): ManagedChannel =
        ManagedChannelBuilder
            .forAddress("127.0.0.1", port)
            .usePlaintext()
            .maxInboundMessageSize(MAX_INBOUND_MESSAGE_SIZE)
            .intercept(RecursionLimitInterceptor)
            .build()

    private object RecursionLimitInterceptor : ClientInterceptor {
        override fun <ReqT, RespT> interceptCall(
            method: MethodDescriptor<ReqT, RespT>,
            callOptions: CallOptions,
            next: Channel,
        ): ClientCall<ReqT, RespT> = next.newCall(method.withDeepResponseMarshaller(), callOptions)
    }

    private fun <ReqT, RespT> MethodDescriptor<ReqT, RespT>.withDeepResponseMarshaller():
        MethodDescriptor<ReqT, RespT> {
        val prototype = (responseMarshaller as? MethodDescriptor.PrototypeMarshaller<*>)
            ?.messagePrototype as? Message
            ?: return this

        @Suppress("UNCHECKED_CAST")
        val marshaller = ProtoUtils.marshallerWithRecursionLimit(prototype, PROTO_RECURSION_LIMIT)
            as MethodDescriptor.Marshaller<RespT>

        return toBuilder().setResponseMarshaller(marshaller).build()
    }
}
