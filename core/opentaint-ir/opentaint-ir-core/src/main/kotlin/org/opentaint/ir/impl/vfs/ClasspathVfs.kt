package org.opentaint.ir.impl.vfs

import org.opentaint.ir.api.jvm.RegisteredLocation
import org.opentaint.ir.impl.LocationsRegistrySnapshot

/**
 * ClassTree view limited by number of `locations`
 */
class ClasspathVfs(
    private val globalClassVFS: GlobalClassesVfs,
    locations: List<RegisteredLocation>
) {

    constructor(globalClassVFS: GlobalClassesVfs, locationsRegistrySnapshot: LocationsRegistrySnapshot) : this(
        globalClassVFS,
        locationsRegistrySnapshot.locations
    )

    private val locationIds: Set<Long> = locations.mapTo(hashSetOf()) { it.id }

    fun findClassNodes(fullName: String): List<ClassVfsItem> {
        return globalClassVFS.findClassNodes(fullName) {
            locationIds.contains(it)
        }
    }
}
