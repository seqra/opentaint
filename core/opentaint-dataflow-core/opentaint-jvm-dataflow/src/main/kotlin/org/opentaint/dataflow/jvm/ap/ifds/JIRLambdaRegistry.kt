package org.opentaint.dataflow.jvm.ap.ifds

import org.opentaint.dataflow.jvm.ap.ifds.LambdaAnonymousClassFeature.JIRLambdaClass
import org.opentaint.ir.api.jvm.JIRMethod
import java.util.concurrent.ConcurrentHashMap

class JIRLambdaRegistry {
    private data class CallSite(val method: JIRMethod, val instIdx: Int)

    private val lambdas = ConcurrentHashMap<CallSite, MutableSet<JIRLambdaClass>>()

    fun register(method: JIRMethod, instIdx: Int, lambda: JIRLambdaClass) {
        lambdas.computeIfAbsent(CallSite(method, instIdx)) { ConcurrentHashMap.newKeySet() }.add(lambda)
    }

    fun registeredLambdas(method: JIRMethod, instIdx: Int): Set<JIRLambdaClass> =
        lambdas[CallSite(method, instIdx)].orEmpty()
}
