package org.opentaint.jvm.sast.dataflow

import org.opentaint.ir.api.jvm.JIRClassOrInterface
import org.opentaint.ir.api.jvm.RegisteredLocation

interface ClassLocationChecker {
    fun isProjectLocation(loc: RegisteredLocation): Boolean
    fun isProjectClass(cls: JIRClassOrInterface): Boolean

    /**
     * The names of every class this checker considers part of the project -- the same set
     * the analysis will treat as analyzable. Used to enumerate the accessor universe for
     * canonical interning; an empty sequence simply degrades that seeding.
     */
    fun projectClassNames(): Sequence<String> = emptySequence()
}
