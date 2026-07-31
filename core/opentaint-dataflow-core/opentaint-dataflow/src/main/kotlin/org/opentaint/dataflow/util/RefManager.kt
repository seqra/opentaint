package org.opentaint.dataflow.util

import java.util.Enumeration
import java.util.concurrent.ConcurrentHashMap

class RefManager {
    private val softRefs = ConcurrentHashMap<String, SoftReferenceManager>()

    fun allSoftRefManagers(): Enumeration<SoftReferenceManager> = softRefs.elements()
    fun softRefManager(name: String): SoftReferenceManager =
        softRefs.computeIfAbsent(name) { SoftReferenceManager(this) }
}
