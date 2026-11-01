package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures

/** Observe the actual post-instruction results for a transfer test. These are
 * body facts, before C5. They confer no summary or persistence permission. */
internal fun MethodAnalysisFixtures.completedBoundary(actor: RunMethodAnalyzer): Sequence<Pair<PremiseKey, Facts>> =
    actor.edges.edgesAt(inst(if (actor.mode.direction == Direction.FORWARD) normalExit else 0))
