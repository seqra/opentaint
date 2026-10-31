package org.opentaint.dataflow.bidi.fixtures

import org.opentaint.dataflow.bidi.interp.*

/** A TRUE sink uses NORMAL ZERO support even while run-1 taint facts are DEMAND. */
fun DriverFixtures.settledNormalSink(): ProgramCase {
    val root = program.method("settled normal sink", listOf(listOf(1), emptyList()), 1).key()
    val sink = SinkRule(rule("settled normal sink"), 0, listOf(ZERO_PATTERN), emptyList())
    program.entry(root, RuleStatement(summary(ZERO_KEEP), StatementSummary.EMPTY, emptyList()))
    program.exit(root, 1, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
        listOf(sink)), false, emptySet()))
    return ProgramCase(root, sink.rule, program.inst(root, 1), ZERO_KEEP)
}
