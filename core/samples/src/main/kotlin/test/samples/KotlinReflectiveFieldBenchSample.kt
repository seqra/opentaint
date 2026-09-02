package test.samples

object KotlinReflectiveFieldBenchSample {

    class Holder {
        @JvmField
        var alpha: String = "clean"

        @JvmField
        var beta: String = "clean"
    }

    fun source(): String = "tainted"

    fun sink(value: String) {}

    fun objectWithoutExtraCleanWriteFlow() {
        val holder = Holder()
        val writeKey = "alpha"
        val readKey = "beta"
        val writeField = Holder::class.java.getDeclaredField(writeKey)
        writeField.set(holder, source())
        val readField = Holder::class.java.getDeclaredField(readKey)
        sink(readField.get(holder) as String)
    }

    fun run() {
        val holder = Holder()
        val writeKey = "alpha"
        val readKey = "beta"
        val writeField = Holder::class.java.getDeclaredField(writeKey)
        writeField.set(holder, source())
        val readField = Holder::class.java.getDeclaredField(readKey)
        readField.set(holder, "clean")
        sink(readField.get(holder) as String)
    }
}
