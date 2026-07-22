package org.opentaint.dataflow.ap.ifds.access.suffix

import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import kotlin.test.Test
import kotlin.test.assertTrue

class FinalSideSummaryCanonicalizerTest {
    private val manager = SuffixTreeApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled)

    @Test
    fun `exclusion widening republishes every retained final branch`() = with(manager) {
        val initial = FieldAccessor("T", "initial", "T").idx
        val first = FieldAccessor("T", "first", "T").idx
        val second = FieldAccessor("T", "second", "T").idx
        val excludedByFirst = FieldAccessor("T", "excludedByFirst", "T").idx
        val commonExclusion = FieldAccessor("T", "commonExclusion", "T").idx
        val excludedBySecond = FieldAccessor("T", "excludedBySecond", "T").idx
        val relation = SuffixRelationTrie()
        val canonicalizer = FinalSideSummaryCanonicalizer(relation, manager)
        val initialAccess = buildInitialPath(listOf(initial))

        canonicalizer.add(
            initialAccess,
            buildFinalPath(
                listOf(initial, first),
                FinalPrefixMarkers(isFinal = false, isAbstract = true),
            )!!,
            setOf(excludedByFirst, commonExclusion),
        )
        val widened = canonicalizer.add(
            initialAccess,
            buildFinalPath(
                listOf(initial, second),
                FinalPrefixMarkers(isFinal = false, isAbstract = true),
            )!!,
            setOf(commonExclusion, excludedBySecond),
        )

        val expectedFirst = relation.factor(
            intArrayOf(initial),
            intArrayOf(initial, first),
            setOf(commonExclusion),
        )
        val expectedSecond = relation.factor(
            intArrayOf(initial),
            intArrayOf(initial, second),
            setOf(commonExclusion),
        )
        assertTrue(relation.isCovered(expectedFirst))
        assertTrue(relation.isCovered(expectedSecond))
        assertTrue(widened.any { relation.isCovered(it) && it.exclusions == setOf(commonExclusion) })
    }

    @Test
    fun `matching conclusion is split from non-identity remainder`() = with(manager) {
        val initial = FieldAccessor("T", "initial", "T").idx
        val child = FieldAccessor("T", "child", "T").idx
        val excluded = FieldAccessor("T", "excluded", "T").idx
        val relation = SuffixRelationTrie()
        val canonicalizer = FinalSideSummaryCanonicalizer(relation, manager)
        val identity = buildFinalPath(
            listOf(initial),
            FinalPrefixMarkers(isFinal = false, isAbstract = true),
        )!!
        val nonIdentity = buildFinalPath(
            listOf(initial, child),
            FinalPrefixMarkers(isFinal = false, isAbstract = true),
        )!!

        canonicalizer.add(
            buildInitialPath(listOf(initial)),
            identity.mergeAdd(nonIdentity),
            setOf(excluded),
        )

        assertTrue(
            relation.isCovered(
                relation.factor(intArrayOf(initial), intArrayOf(initial), setOf(excluded))
            )
        )
        assertTrue(
            relation.isCovered(
                relation.factor(
                    intArrayOf(initial),
                    intArrayOf(initial, child),
                    setOf(excluded),
                )
            )
        )
    }
}
