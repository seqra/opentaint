package test.samples

class KotlinReflectiveFieldSample {

    class Holder {
        @JvmField
        var alpha: String = "clean"

        @JvmField
        var beta: String = "clean"
    }

    fun reflectiveSameFieldFlow() {
        val holder = Holder()
        val writeKey = "alpha"
        val writeField = Holder::class.java.getDeclaredField(writeKey)
        writeField.set(holder, source())
        val readField = Holder::class.java.getDeclaredField(writeKey)
        sink(readField.get(holder) as String)
    }

    fun reflectiveOtherFieldFlow() {
        val holder = Holder()
        val writeKey = "alpha"
        val readKey = "beta"
        val writeField = Holder::class.java.getDeclaredField(writeKey)
        writeField.set(holder, source())
        val readField = Holder::class.java.getDeclaredField(readKey)
        sink(readField.get(holder) as String)
    }

    fun classWithExtraCleanWriteFlow() {
        val holder = Holder()
        val writeKey = "alpha"
        val readKey = "beta"
        val writeField = Holder::class.java.getDeclaredField(writeKey)
        writeField.set(holder, source())
        val readField = Holder::class.java.getDeclaredField(readKey)
        readField.set(holder, "clean")
        sink(readField.get(holder) as String)
    }

    fun source(): String = "tainted"

    fun sink(value: String) {}
}
