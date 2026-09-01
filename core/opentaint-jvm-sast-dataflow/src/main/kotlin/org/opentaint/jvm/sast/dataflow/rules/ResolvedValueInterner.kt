package org.opentaint.jvm.sast.dataflow.rules

internal class ResolvedValueInterner<T : Any> {
    private val values = hashMapOf<T, T>()

    @Synchronized
    fun intern(value: T): T = values.getOrPut(value) { value }
}
