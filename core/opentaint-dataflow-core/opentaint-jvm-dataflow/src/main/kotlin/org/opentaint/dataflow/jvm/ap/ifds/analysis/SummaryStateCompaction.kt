package org.opentaint.dataflow.jvm.ap.ifds.analysis

internal inline fun <S : Any, K> MutableMap<K, S>.retainCanonicalSummaryState(
    state: S?,
    key: (S) -> K,
) {
    if (state != null) putIfAbsent(key(state), state)
}
