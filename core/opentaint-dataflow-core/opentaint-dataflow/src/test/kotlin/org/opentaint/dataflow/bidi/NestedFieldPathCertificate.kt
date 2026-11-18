package org.opentaint.dataflow.bidi

/** Test implementation of the finite state-pair certificate for one nested side. */
internal object NestedFieldPathCertificate {
    data class Rule(val owner: Int, val lead: List<Int>, val next: Int?, val suffix: List<Int> = emptyList())
    data class Cell(val owner: Int, val start: Int, val end: Int)

    fun disjoint(
        rules: List<Rule>,
        owners: Int,
        automaton: RegularFieldPathQuery.Nfa,
        outerSuffix: List<Int>,
        completeSlice: Boolean,
    ): Boolean? {
        if (!completeSlice || owners <= 0 || rules.any {
                it.owner !in 0 until owners || it.next?.let { next -> next !in 0 until owners } == true
            }) return null
        val states = (listOf(automaton.start) + automaton.finals +
            automaton.arcs.flatMap { listOf(it.from, it.to) }).toSet()
        fun consequences(cells: Set<Cell>): Set<Cell> = buildSet {
            for (rule in rules) for (start in states) {
                val entered = automaton.ends(start, rule.lead)
                if (rule.next == null) {
                    for (end in entered) add(Cell(rule.owner, start, end))
                } else {
                    for (cell in cells) if (cell.owner == rule.next && cell.start in entered) {
                        for (end in automaton.ends(cell.end, rule.suffix)) add(Cell(rule.owner, start, end))
                    }
                }
            }
        }
        val cells = linkedSetOf<Cell>()
        while (cells.addAll(consequences(cells))) {
            // Each change adds a new cell in the finite owner × state × state domain.
        }
        check(cells.containsAll(consequences(cells)))
        return cells.none {
            it.owner == 0 && it.start == automaton.start &&
                automaton.ends(it.end, outerSuffix).any(automaton.finals::contains)
        }
    }
}
