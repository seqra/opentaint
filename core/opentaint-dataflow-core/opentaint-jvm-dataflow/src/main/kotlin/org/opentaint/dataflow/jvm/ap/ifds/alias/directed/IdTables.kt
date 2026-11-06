package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap
import java.util.BitSet

/**
 * Gives one id to each key. The ids start at [firstId] and are dense.
 * After [freeze], a lookup of a known key works, and a new key causes [IllegalStateException].
 */
internal class KeyTable<K : Any>(private val firstId: Int, private val name: String) {
    private val ids = Object2IntOpenHashMap<K>().also { it.defaultReturnValue(NO_ID) }
    private val keys = ArrayList<K>()
    private var frozen = false

    val size: Int get() = keys.size

    fun id(key: K): Int {
        val known = ids.getInt(key)
        if (known != NO_ID) return known
        check(!frozen) { "$name is frozen: no new id for $key" }
        val id = firstId + keys.size
        keys.add(key)
        ids.put(key, id)
        return id
    }

    fun find(key: K): Int = ids.getInt(key)

    fun key(id: Int): K = keys[id - firstId]

    fun freeze() {
        frozen = true
    }
}

/**
 * The cells (IMPL §3.1). [ELEM_CELL] is id 0. Each field (class name, field name, type) gets an id
 * from 1.
 */
class CellTable {
    data class FieldKey(val className: String, val fieldName: String, val type: String)

    private val fields = KeyTable<FieldKey>(firstId = ELEM_CELL + 1, name = "CellTable")

    /** The number of cells, [ELEM_CELL] included. */
    val size: Int get() = fields.size + 1

    fun field(className: String, fieldName: String, type: String): CellId =
        fields.id(FieldKey(className, fieldName, type))

    /** The key of a field cell, or `null` for [ELEM_CELL]. */
    fun fieldKey(c: CellId): FieldKey? = if (c == ELEM_CELL) null else fields.key(c)

    fun freeze() = fields.freeze()
}

/**
 * The variables (IMPL §3.1). The ids 0 and 1 are the reserved keys [ETREE] and [EVAL]. Each pair
 * (local index, context) gets an id from 2.
 */
class VarTable {
    data class LocalKey(val index: Int, val context: Int)

    private val locals = KeyTable<LocalKey>(firstId = EVAL + 1, name = "VarTable")

    val size: Int get() = locals.size + 2

    fun local(index: Int, context: Int = ROOT_CONTEXT): VarId = locals.id(LocalKey(index, context))

    /** The key of a local, or `null` for a reserved key. */
    fun key(v: VarId): LocalKey? = if (isReserved(v)) null else locals.key(v)

    fun isReserved(v: VarId): Boolean = v == ETREE || v == EVAL

    fun freeze() = locals.freeze()
}

/**
 * The sites (IMPL §3.2). Each pair (instruction index, context) gets an id from 0. The null site of
 * a statement is its site.
 *
 * A site is a loop site if its node is on a cycle of the alias CFG (IMPL §5.4). The CFG builder
 * marks the loop sites with [markLoopSite] before the fixpoint. Only a loop site retires (IMPL §4.3),
 * and the fresh origins of a loop site are not unique.
 */
class SiteTable {
    data class SiteKey(val instIndex: Int, val context: Int)

    private val sites = KeyTable<SiteKey>(firstId = 0, name = "SiteTable")
    private val loopSites = BitSet()
    private var frozen = false

    val size: Int get() = sites.size

    fun site(instIndex: Int, context: Int = ROOT_CONTEXT): SiteId = sites.id(SiteKey(instIndex, context))

    fun key(s: SiteId): SiteKey = sites.key(s)

    fun markLoopSite(s: SiteId) {
        check(!frozen) { "SiteTable is frozen" }
        loopSites.set(s)
    }

    fun isLoopSite(s: SiteId): Boolean = loopSites.get(s)

    fun freeze() {
        frozen = true
        sites.freeze()
    }
}
