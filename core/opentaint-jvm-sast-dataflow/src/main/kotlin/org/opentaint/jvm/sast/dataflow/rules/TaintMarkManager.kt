package org.opentaint.jvm.sast.dataflow.rules

import org.opentaint.dataflow.configuration.jvm.TaintMark
import java.util.concurrent.ConcurrentHashMap

class TaintMarkManager {
    private val taintMarks = ConcurrentHashMap<String, TaintMark>()

    fun taintMark(name: String): TaintMark = taintMarks.computeIfAbsent(name) { TaintMark(it) }
}
