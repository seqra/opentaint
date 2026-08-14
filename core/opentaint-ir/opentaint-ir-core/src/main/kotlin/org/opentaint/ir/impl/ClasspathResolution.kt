package org.opentaint.ir.impl

import org.opentaint.ir.api.jvm.ClassSource
import org.opentaint.ir.api.jvm.JIRClasspathResolution
import org.opentaint.ir.api.jvm.LocationType
import org.opentaint.ir.api.jvm.RegisteredLocation

/**
 * Selects one class definition using location type and the caller's classpath order.
 *
 * Candidates from multiple stores may be supplied in preference order. If the same
 * registered location occurs more than once, its first candidate is retained.
 */
internal class ClasspathResolution(locations: List<RegisteredLocation>): JIRClasspathResolution {

    private data class LocationRank(val score: Int, val classpathPosition: Int)

    private val rankByLocationId: Map<Long, LocationRank> = buildMap {
        locations.forEachIndexed { index, location ->
            putIfAbsent(location.id, LocationRank(location.type.resolutionScore(), index))
        }
    }

    override fun selectClassSource(candidates: Sequence<ClassSource>): ClassSource? =
        select(candidates) { it.location.id }

    override fun distinctClassSources(candidates: Sequence<ClassSource>): List<ClassSource> =
        distinct(candidates) { it.location.id }

    private inline fun <T> select(candidates: Sequence<T>, locationId: (T) -> Long): T? {
        var winner: T? = null
        var winnerRank: LocationRank? = null
        val seenLocations = hashSetOf<Long>()

        candidates.forEach { candidate ->
            val id = locationId(candidate)
            if (!seenLocations.add(id)) return@forEach
            val rank = rankByLocationId[id] ?: return@forEach

            val currentWinnerRank = winnerRank
            if (currentWinnerRank == null || rank outranks currentWinnerRank) {
                winner = candidate
                winnerRank = rank
            }
        }
        return winner
    }

    private inline fun <T> distinct(candidates: Sequence<T>, crossinline locationId: (T) -> Long): List<T> {
        val seenLocations = hashSetOf<Long>()
        return candidates.filter { candidate ->
            val id = locationId(candidate)
            rankByLocationId.containsKey(id) && seenLocations.add(id)
        }.toList()
    }

    private infix fun LocationRank.outranks(other: LocationRank): Boolean =
        score > other.score || score == other.score && classpathPosition < other.classpathPosition
}

/** Keep resolution policy local to class lookup rather than exposing it on [LocationType]. */
private fun LocationType.resolutionScore(): Int = when (this) {
    LocationType.APP -> 3
    LocationType.LIB -> 2
    LocationType.RUNTIME -> 1
}
