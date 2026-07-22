package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.access.automata.AutomataApManager
import org.opentaint.dataflow.ap.ifds.access.cactus.CactusApManager
import org.opentaint.dataflow.ap.ifds.access.suffix.SuffixTreeApManager
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager

enum class ApMode {
    Tree, Cactus, Automata, SuffixTree;

    fun createApManager(unrollStrategy: AnyAccessorUnrollStrategy): ApManager = when (this) {
        Tree -> TreeApManager(unrollStrategy)
        Cactus -> CactusApManager(unrollStrategy)
        Automata -> AutomataApManager(unrollStrategy)
        SuffixTree -> SuffixTreeApManager(unrollStrategy)
    }

    companion object {
        fun fromTestProperty(default: ApMode = Tree): ApMode {
            val raw = System.getProperty("opentaint.test.apMode") ?: return default
            return entries.firstOrNull { it.name.equals(raw, ignoreCase = true) }
                ?: error("Unknown opentaint.test.apMode='$raw'; expected one of ${entries.map { it.name }}")
        }
    }
}
