package org.opentaint.dataflow.ap.ifds.access.suffix

import java.util.Collections
import java.util.WeakHashMap
import java.util.concurrent.atomic.AtomicLong

/** Low-overhead shape counters and opt-in expensive summary-language verification. */
object SuffixTreeDiagnostics {
    data class Snapshot(
        val publishedBundles: Long,
        val publishedCones: Long,
        val nonEmptySuffixBundles: Long,
        val branchingSuffixBundles: Long,
        val branchingIdentityBundles: Long,
        val storedRelationsWithNonEmptySuffix: Long,
        val storedRelationsWithBranchingSuffix: Long,
        val storedRelationsWithBranchingIdentity: Long,
    )

    internal val verifySummaries: Boolean
        get() = java.lang.Boolean.getBoolean("opentaint.suffix.verify")

    private val logShapes: Boolean
        get() = java.lang.Boolean.getBoolean("opentaint.suffix.logShapes")

    private val publishedBundles = AtomicLong()
    private val publishedCones = AtomicLong()
    private val nonEmptySuffixBundles = AtomicLong()
    private val branchingSuffixBundles = AtomicLong()
    private val branchingIdentityBundles = AtomicLong()
    private val storedRelationsWithNonEmptySuffix = AtomicLong()
    private val storedRelationsWithBranchingSuffix = AtomicLong()
    private val storedRelationsWithBranchingIdentity = AtomicLong()
    // Diagnostics must not extend the lifetime of per-method relations; SuffixRelationTrie keeps
    // identity equality, so weak keys also preserve the intended per-instance bookkeeping.
    private val loggedShapes = Collections.synchronizedMap(WeakHashMap<SuffixRelationTrie, Int>())

    fun snapshot(): Snapshot = Snapshot(
        publishedBundles.get(),
        publishedCones.get(),
        nonEmptySuffixBundles.get(),
        branchingSuffixBundles.get(),
        branchingIdentityBundles.get(),
        storedRelationsWithNonEmptySuffix.get(),
        storedRelationsWithBranchingSuffix.get(),
        storedRelationsWithBranchingIdentity.get(),
    )

    internal fun recordPublished(
        bundle: SuffixEdgeBundle,
        identity: Boolean,
    ) {
        val cones = bundle.suffixTree.cones()
        val nonEmpty = cones.any { it.suffix.isNotEmpty() }
        val branching = bundle.suffixTree.isBranching()
        publishedBundles.incrementAndGet()
        publishedCones.addAndGet(cones.size.toLong())
        if (nonEmpty) nonEmptySuffixBundles.incrementAndGet()
        if (branching) branchingSuffixBundles.incrementAndGet()
        if (identity && branching) branchingIdentityBundles.incrementAndGet()

    }

    internal fun logStoredShape(
        relation: SuffixRelationTrie,
        identity: (SuffixEdgeBundle) -> Boolean,
        site: () -> String,
    ) {
        if (!logShapes) return
        var observed = loggedShapes[relation] ?: 0
        for (bundle in relation.bundles()) {
            val nonEmpty = bundle.suffixTree.hasNonEmptySuffix()
            val branching = bundle.suffixTree.isBranching()
            val isIdentity = identity(bundle)
            val features =
                (if (nonEmpty) NON_EMPTY_SUFFIX else 0) or
                    (if (branching) BRANCHING_SUFFIX else 0) or
                    (if (branching && isIdentity) BRANCHING_IDENTITY else 0)
            val newlyObserved = features and observed.inv()
            if (newlyObserved == 0) continue
            if (newlyObserved and NON_EMPTY_SUFFIX != 0) {
                storedRelationsWithNonEmptySuffix.incrementAndGet()
            }
            if (newlyObserved and BRANCHING_SUFFIX != 0) {
                storedRelationsWithBranchingSuffix.incrementAndGet()
            }
            if (newlyObserved and BRANCHING_IDENTITY != 0) {
                storedRelationsWithBranchingIdentity.incrementAndGet()
            }
            println(
                "SuffixTree stored shape at ${site()}: initial=${bundle.initialPrefix}, " +
                    "finals=${bundle.finalPrefixTree.terminals().map { it.prefix }}, " +
                    "suffixes=${bundle.suffixTree.cones().map { it.suffix }}, " +
                    "identity=$isIdentity, newFeatures=${featureNames(newlyObserved)}"
            )
            observed = observed or features
            loggedShapes[relation] = observed
        }
    }

    private fun featureNames(features: Int): List<String> = buildList {
        if (features and NON_EMPTY_SUFFIX != 0) add("non-empty-suffix")
        if (features and BRANCHING_SUFFIX != 0) add("branching-suffix-tree")
        if (features and BRANCHING_IDENTITY != 0) add("branching-identity-bundle")
    }

    private const val NON_EMPTY_SUFFIX = 1
    private const val BRANCHING_SUFFIX = 2
    private const val BRANCHING_IDENTITY = 4
}
