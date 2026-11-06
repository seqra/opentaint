package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

/** The type of the constant key of a string literal. */
const val STRING_TYPE: String = "java.lang.String"

/** The type of the constant key of a class literal. */
const val CLASS_TYPE: String = "java.lang.Class"

/** The kind of the base of a symbolic origin (IMPL §3.2). */
enum class BaseKind { THIS, ARG, STATIC, FRESH, CONST, BOX, NULL, ALLOC_CHILD }

/** The key of a base. Two equal keys give one base. */
sealed interface BaseKey {
    val kind: BaseKind

    /** The entry root `this`. */
    data object This : BaseKey {
        override val kind: BaseKind get() = BaseKind.THIS
    }

    /** The entry root of argument [index]. */
    data class Arg(val index: Int) : BaseKey {
        override val kind: BaseKind get() = BaseKind.ARG
    }

    /** The static holder of the class with the binary name [className]. */
    data class Static(val className: String) : BaseKey {
        override val kind: BaseKind get() = BaseKind.STATIC
    }

    /** The result of an unresolved call, of a catch, or of an unknown expression at [site]. */
    data class Fresh(val site: SiteId) : BaseKey {
        override val kind: BaseKind get() = BaseKind.FRESH
    }

    /**
     * An interned constant: a string ([STRING_TYPE], value), a class literal ([CLASS_TYPE], class
     * name), a box of a constant (box type, constant text), or another constant (type, text).
     */
    data class Const(val type: String, val text: String) : BaseKey {
        override val kind: BaseKind get() = BaseKind.CONST
    }

    /** A box of a value that is not a constant, at [site] (I3). */
    data class Box(val site: SiteId) : BaseKey {
        override val kind: BaseKind get() = BaseKind.BOX
    }

    /** The null of the null assignment at [site]. */
    data class Null(val site: SiteId) : BaseKey {
        override val kind: BaseKind get() = BaseKind.NULL
    }

    /** The value in cell [cell] of an object of the allocation site [site]: `⟨@s.c⟩`. */
    data class AllocChild(val site: SiteId, val cell: CellId) : BaseKey {
        override val kind: BaseKind get() = BaseKind.ALLOC_CHILD
    }
}

/**
 * The bases of the symbolic origins. Each [BaseKey] gets one id from 0.
 *
 * The table also records the type name of each static holder at its first static read. The
 * answer uses this name (IMPL §1.3, §4.1).
 */
class BaseTable {
    private val bases = KeyTable<BaseKey>(firstId = 0, name = "BaseTable")
    private val staticTypeNames = HashMap<BaseId, String>()

    val size: Int get() = bases.size

    fun intern(key: BaseKey): BaseId = bases.id(key)

    fun key(b: BaseId): BaseKey = bases.key(b)

    fun kind(b: BaseId): BaseKind = bases.key(b).kind

    fun thisBase(): BaseId = intern(BaseKey.This)

    fun arg(index: Int): BaseId = intern(BaseKey.Arg(index))

    /**
     * The static holder of [className] (a binary class name). If [typeName] is not `null` and the
     * table has no type name for this class, the table records [typeName].
     */
    fun static(className: String, typeName: String? = null): BaseId {
        val b = intern(BaseKey.Static(className))
        if (typeName != null) staticTypeNames.putIfAbsent(b, typeName)
        return b
    }

    /** The recorded type name of a static holder, or `null`. */
    fun staticTypeName(b: BaseId): String? = staticTypeNames[b]

    fun fresh(site: SiteId): BaseId = intern(BaseKey.Fresh(site))

    fun const(type: String, text: String): BaseId = intern(BaseKey.Const(type, text))

    fun box(site: SiteId): BaseId = intern(BaseKey.Box(site))

    fun nullAt(site: SiteId): BaseId = intern(BaseKey.Null(site))

    fun allocChild(site: SiteId, cell: CellId): BaseId = intern(BaseKey.AllocChild(site, cell))

    /** As [allocChild], but [NO_ID] if the base does not exist. It never makes a base. */
    fun findAllocChild(site: SiteId, cell: CellId): BaseId = bases.find(BaseKey.AllocChild(site, cell))

    fun freeze() = bases.freeze()
}
