package test.samples

class KotlinReflectiveInvocationSample {

    fun leak(value: String) {
        sink(value)
    }

    fun drop(value: String) {
        sink("clean")
    }

    fun directInvocationFlow() {
        leak(source())
    }

    fun reflectiveLeakFlow() {
        val name = "leak"
        val method = KotlinReflectiveInvocationSample::class.java.getMethod(name, String::class.java)
        method.invoke(this, source())
    }

    fun reflectiveDropFlow() {
        val name = "drop"
        val method = KotlinReflectiveInvocationSample::class.java.getMethod(name, String::class.java)
        method.invoke(this, source())
    }

    fun reflectiveUnresolvedFlow(externalName: String) {
        val method = KotlinReflectiveInvocationSample::class.java.getMethod(externalName, String::class.java)
        method.invoke(this, source())
    }

    fun source(): String = "tainted"

    fun sink(value: String) {}
}
