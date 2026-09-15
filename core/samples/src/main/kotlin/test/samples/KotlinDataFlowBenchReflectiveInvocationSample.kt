package test.samples

class KotlinDataFlowBenchReflectiveInvocationSample {
    fun leak(value: String) {
        sink(value)
    }

    fun reflectiveInvocationFlow() {
        val receiver = KotlinDataFlowBenchReflectiveInvocationSample()
        val name = "leak"
        val method = KotlinDataFlowBenchReflectiveInvocationSample::class.java
            .getMethod(name, String::class.java)
        method.invoke(receiver, source())
    }

    fun directInvocationFlow() {
        val receiver = KotlinDataFlowBenchReflectiveInvocationSample()
        receiver.leak(source())
    }

    fun source(): String = "tainted"
    fun sink(data: String) {}
}
