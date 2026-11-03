package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.Facts
import org.opentaint.dataflow.bidi.ap.GroupKey

/** The same table used by live local delivery; it has no callback or runtime owner. */
internal data class LocalInputKey(val link: LocalLink, val group: GroupKey)
internal data class LocalInputValue(val link: LocalLink, var value: Facts)
internal class LocalInputDirectory {
    private val rows = LinkedHashMap<LocalInputKey, LocalInputValue>()
    val size: Int get() = rows.size
    val values: Collection<LocalInputValue> get() = rows.values
    operator fun get(key: LocalInputKey): LocalInputValue? = rows[key]
    operator fun set(key: LocalInputKey, value: LocalInputValue) { rows[key] = value }
    fun clear() = rows.clear()
}

/** Joined ownership of one moved input directory, including saved-only entries. */
internal class JoinedLocalInputs internal constructor(private var directory: LocalInputDirectory?) : AutoCloseable {
    internal val groups: Int get() = checkNotNull(directory) { "Joined local inputs are closed" }.size
    fun visit(visit: (LocalLink, Facts) -> Unit) {
        for (input in checkNotNull(directory) { "Joined local inputs are closed" }.values)
            visit(input.link, input.value)
    }
    override fun close() {
        val owned = directory ?: return
        directory = null
        owned.clear()
    }
}
