package org.opentaint.dataflow.util

import org.opentaint.dataflow.util.TrackerWithSubscriber.Subscriber

abstract class TrackerWithSubscriber<K, V, S: Subscriber<K, V>>(val key: K) {
    interface Subscriber<K, V> {
        fun handle(key: K, value: V)
    }

    private val subscribers = hashSetOf<S>()
    private val registeredValues = hashSetOf<V>()

    fun addValue(value: V) = synchronized(this) {
        if (!registeredValues.add(value)) return
        subscribers.forEach { it.handle(key, value) }
    }

    fun addSubscriber(subscriber: S) = synchronized(this) {
        if (!subscribers.add(subscriber)) return
        registeredValues.forEach { subscriber.handle(key, it) }
    }

    fun forEachRegisteredValue(subscriber: S) = synchronized(this) {
        registeredValues.forEach { subscriber.handle(key, it) }
    }
}
