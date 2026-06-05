package org.opentaint.dataflow.jvm.ap.ifds

import org.opentaint.dataflow.jvm.ap.ifds.LambdaAnonymousClassFeature.JIRLambdaClass
import org.opentaint.dataflow.util.TrackerWithSubscriber
import org.opentaint.ir.api.jvm.JIRMethod

object JIRLambdaTracker {
    class LambdaTracker(method: JIRMethod) :
        TrackerWithSubscriber<JIRMethod, JIRLambdaClass, LambdaSubscriber>(method) {
        val method: JIRMethod get() = key
        fun addLambda(lambda: JIRLambdaClass) = addValue(lambda)
        fun forEachRegisteredLambda(subscriber: LambdaSubscriber) = forEachRegisteredValue(subscriber)
    }

    interface LambdaSubscriber : TrackerWithSubscriber.Subscriber<JIRMethod, JIRLambdaClass> {
        fun newLambda(method: JIRMethod, lambdaClass: JIRLambdaClass)
        override fun handle(key: JIRMethod, value: JIRLambdaClass) = newLambda(key, value)
    }
}
