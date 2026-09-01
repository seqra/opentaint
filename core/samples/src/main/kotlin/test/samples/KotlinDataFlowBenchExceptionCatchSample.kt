package test.samples

class KotlinDataFlowBenchExceptionCatchSample {
    class IntFlowException : RuntimeException() {
        var value: Int = 0
    }

    class StringFlowException : RuntimeException() {
        var value: String = ""
    }

    fun exceptionCatchIntFlow() {
        try {
            val flow = IntFlowException()
            flow.value = intSource()
            throw flow
        } catch (caught: IntFlowException) {
            intSink(caught.value)
        }
    }

    fun exceptionCatchStringFlow() {
        try {
            val flow = StringFlowException()
            flow.value = source()
            throw flow
        } catch (caught: StringFlowException) {
            sink(caught.value)
        }
    }

    fun carrierFieldFlow() {
        val flow = StringFlowException()
        flow.value = source()
        sink(flow.value)
    }

    fun intSource(): Int = 1
    fun intSink(data: Int) {}
    fun source(): String = "tainted"
    fun sink(data: String) {}
}
