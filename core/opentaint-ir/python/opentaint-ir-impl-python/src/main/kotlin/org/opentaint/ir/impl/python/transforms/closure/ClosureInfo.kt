package org.opentaint.ir.impl.python.transforms.closure

/**
 * - [ownedNames] — names this function defines: parameters plus locals
 *   it actually owns (writes that aren't `nonlocal` / `global`).
 * - [cellVars] — owned names that must be cell-allocated because some
 *   descendant captures them.
 * - [closureVars] — names this function must receive from its parent's
 *   closure environment. Always empty when [isClosureRoot] is true.
 * - [isClosureRoot] — `true` iff the function has no closure parent
 *   (top-level free function, module init, method of a top-level/module-level class).
 */
data class ClosureInfo(
    val ownedNames: Set<String>,
    val cellVars: Set<String>,
    val closureVars: Set<String>,
    val isClosureRoot: Boolean,
)
