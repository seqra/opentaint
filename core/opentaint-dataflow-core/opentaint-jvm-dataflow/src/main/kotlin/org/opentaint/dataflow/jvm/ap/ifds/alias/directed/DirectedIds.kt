package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

/*
 * The ids of the directed alias engine (IMPL §3.1).
 * The engine core does not use JIR. All ids are indexes in the tables of one method analysis.
 */

/** An origin: an abstract value (spec §3). [OriginTable] gives the ids. */
typealias OriginId = Int

/** A node: one origin set in canonical form. [NodeTable] gives the ids. */
typealias NodeId = Int

/** A cell: a field, or [ELEM_CELL] for all elements of an array. [CellTable] gives the ids. */
typealias CellId = Int

/** A variable: a local in a context, or a reserved key. [VarTable] gives the ids. */
typealias VarId = Int

/** A site: an instruction in a context. [SiteTable] gives the ids. */
typealias SiteId = Int

/** The base of a symbolic origin. [BaseTable] gives the ids. */
typealias BaseId = Int

/** The key of a heap entry: an origin and a cell in one `Long`. */
typealias HeapKey = Long

/** The node of the empty set. */
const val EMPTY_NODE: NodeId = 0

/** The cell of all elements of an array. */
const val ELEM_CELL: CellId = 0

/** The reserved env key of `Etree`: the origins that a call reached (spec §5.6). */
const val ETREE: VarId = 0

/** The reserved env key of `Eval`: the origins found in a cell of a reached origin (spec §5.6). */
const val EVAL: VarId = 1

/** The context of the analyzed method. An inlined callee has another context. */
const val ROOT_CONTEXT: Int = 0

/** No id. A table gives this value for an absent entry. */
const val NO_ID: Int = -1

@Suppress("NOTHING_TO_INLINE")
inline fun heapKey(o: OriginId, c: CellId): HeapKey = (o.toLong() shl 32) or (c.toLong() and 0xFFFF_FFFFL)

@Suppress("NOTHING_TO_INLINE")
inline fun heapKeyOrigin(k: HeapKey): OriginId = (k ushr 32).toInt()

@Suppress("NOTHING_TO_INLINE")
inline fun heapKeyCell(k: HeapKey): CellId = k.toInt()
