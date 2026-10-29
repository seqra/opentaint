package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.fixtures.PipelineFixtures
import org.opentaint.dataflow.bidi.fixtures.QueuedProtocolSteps
import org.opentaint.dataflow.bidi.store.CallerRef
import kotlin.test.*

/** Operation counts use the real indexes and AP predicate; this is not a timing benchmark. */
class SummaryCandidateWorkloadTest {
    @Test
    fun `mark-blind candidate lookup expands every output before it rejects an unrelated premise`(): Unit {
        MethodAnalysisFixtures().use { f ->
            val markCount = 32
            val outputsPerPremise = 16
            val mode = f.config(index = 3).mode
            val publications = PublicationIndex(f.manager, f.ops, flowBacked = true)
            val inputs = CalleeSubscriptions(f.ops)
            val callee = f.store.key("workload callee")
            val marks = (0 until markCount).map { MarkSlot.Concrete(f.store.mark("T$it")) }
            val parts = marks.mapIndexed { i, mark ->
                val added = f.store.fact(mark = mark)
                Subscription(callee,
                    CallerRef(f.key, f.manager.zero, Layer.NORMAL, f.store.inst(i + 1)),
                    added.layer, added)
            }
            val offered = marks.flatMap { mark ->
                val initial = f.manager.initial(f.store.pattern(mark = mark))
                (0 until outputsPerPremise).map { output ->
                    Publication(initial, f.store.fact(base = AccessPathBase.Argument(output + 1), mark = mark))
                }
            }
            val delta = publications.addAll(offered)
            assertEquals(markCount * outputsPerPremise, delta.size)
            parts.forEach { assertNotNull(inputs.add(it)) }

            var replayCandidates = 0
            var replayMatches = 0
            var uniqueReplayPremiseTests = 0
            for (part in parts) {
                val candidates = publications.candidates(part, mode)
                replayCandidates += candidates.size
                uniqueReplayPremiseTests += candidates.map { (pub, member) -> pub.premise.member(member) }.toSet().size
                replayMatches += candidates.count { (pub, member) -> matches(part, pub, member, f.ops, mode) != null }
            }

            var deliveryCandidates = 0
            var deliveryMatches = 0
            for (pub in delta) {
                val candidates = inputs.candidates(pub, 0, mode).toList()
                deliveryCandidates += candidates.size
                deliveryMatches += candidates.count { matches(it, pub, 0, f.ops, mode) != null }
            }

            // The AP positions are equal, but only T_i can satisfy the premise T_i.
            // Current replay materializes all M outputs for each wrong T_j before matching.
            val allCandidatePairs = markCount * markCount * outputsPerPremise
            val actualMatches = markCount * outputsPerPremise
            assertEquals(16_384, allCandidatePairs)
            assertEquals(512, actualMatches)
            assertEquals(allCandidatePairs, replayCandidates)
            assertEquals(actualMatches, replayMatches)
            assertEquals(allCandidatePairs, deliveryCandidates)
            assertEquals(actualMatches, deliveryMatches)
            // Matching depends on input and premise, not on the output group.
            assertEquals(markCount * markCount, uniqueReplayPremiseTests)
            assertEquals(outputsPerPremise * uniqueReplayPremiseTests, replayCandidates)
        }
    }

    @Test
    fun `one premise with many output groups repeats an identical applicability predicate`(): Unit {
        MethodAnalysisFixtures().use { f ->
            val outputs = 32
            val mode = f.config(index = 3).mode
            val storage = PublicationIndex(f.manager, f.ops, flowBacked = true)
            val mark = MarkSlot.Concrete(f.store.mark("T"))
            val initial = f.manager.initial(f.store.pattern(mark = mark))
            val pubs = (1..outputs).map { target ->
                Publication(initial, f.store.fact(base = AccessPathBase.Argument(target), mark = mark))
            }
            assertEquals(outputs, storage.addAll(pubs).size)
            val added = f.store.fact(mark = mark)
            val part = Subscription(f.store.key("fanout callee"),
                CallerRef(f.key, f.manager.zero, Layer.NORMAL, f.store.inst(1)), added.layer, added)
            val candidates = storage.candidates(part, mode)
            assertEquals(outputs, candidates.size)
            assertEquals(setOf(initial), candidates.map { (pub, member) -> pub.premise.member(member) }.toSet())
            val selected = candidates.map { (pub, member) -> assertNotNull(matches(part, pub, member, f.ops, mode)) }
            assertEquals(1, selected.toSet().size,
                "All 32 filters have exactly the same input, premise and result; the output work is distinct")
        }
    }

    @Test
    fun `a publication between registration and replay can apply the same pair through both channels`(): Unit {
        val steps = QueuedProtocolSteps()
        PipelineFixtures(index = 3, protocol = steps).use { f ->
            val part = f.subscription()
            val pub = Publication(f.ap.initial(f.store.pattern()), f.store.fact(base = AccessPathBase.Return))
            f.subscriptions.subscribe(part)
            f.storage().publish(listOf(pub))
            steps.runNotifications()
            f.deliverAll()
            assertEquals(1, f.summaries.size)
            steps.replayAll()
            assertEquals(2, f.summaries.size)
            assertEquals(1, f.summaries.map { Triple(it.part, it.publication, it.member) }.toSet().size)
            // This is a legal arrival order, not a project-scale duplicate-rate measurement.
        }
    }
}
