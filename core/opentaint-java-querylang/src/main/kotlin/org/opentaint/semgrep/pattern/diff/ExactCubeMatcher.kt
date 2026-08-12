package org.opentaint.semgrep.pattern.diff

/** Cancels structurally equal DNF cubes one-for-one before any automata are built. */
object ExactCubeMatcher {
    fun match(old: List<ContextualCube>, new: List<ContextualCube>): CubeDiffPlan {
        val remainingNew = new.indices.toMutableSet()
        val matches = mutableListOf<CubeMatch>()
        val unmatchedOld = mutableListOf<ContextualCube>()

        for (oldCube in old.sortedWith(contextualCubeComparator)) {
            val candidates = remainingNew
                .asSequence()
                .filter { new[it].cube.key == oldCube.cube.key }
                .sortedWith(
                    compareBy<Int>(
                        { new[it].declarationKind != oldCube.declarationKind },
                        { new[it].declarationOrdinal != oldCube.declarationOrdinal },
                        { new[it].ownerRuleId },
                        { new[it].declarationKind.ordinal },
                        { new[it].declarationOrdinal },
                        { new[it].cube.ordinal },
                    )
                )
                .toList()

            val newIndex = candidates.firstOrNull()
            if (newIndex == null) {
                unmatchedOld += oldCube
                continue
            }

            remainingNew.remove(newIndex)
            matches += CubeMatch(oldCube, new[newIndex], CubeMatch.Kind.EXACT)
        }

        return CubeDiffPlan(
            exactMatches = matches.sortedWith(compareBy({ it.old.ownerRuleId }, { it.old.declarationKind }, { it.old.declarationOrdinal }, { it.old.cube.ordinal })),
            unmatchedOld = unmatchedOld.sortedWith(contextualCubeComparator),
            unmatchedNew = remainingNew.map { new[it] }.sortedWith(contextualCubeComparator),
        )
    }

    private val contextualCubeComparator = compareBy<ContextualCube>(
        { it.ownerRuleId },
        { it.declarationKind.ordinal },
        { it.declarationOrdinal },
        { it.cube.ordinal },
        { it.cube.key.toString() },
    )
}
