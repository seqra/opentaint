package org.opentaint.dataflow.ap.ifds.analysis.alias

class DsuMergeStrategy(private val manager: AAInfoManager) : IntDisjointSets.RankStrategy {
    override fun compare(a: Int, b: Int): Int =
        manager.getElementUncheck(a).compareTo(manager.getElementUncheck(b))
}
