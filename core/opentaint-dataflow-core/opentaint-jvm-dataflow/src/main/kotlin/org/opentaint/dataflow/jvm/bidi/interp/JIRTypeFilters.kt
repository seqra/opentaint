package org.opentaint.dataflow.jvm.bidi.interp

import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.bidi.ap.ApManager
import org.opentaint.dataflow.bidi.ap.LevelMarkPolicy
import org.opentaint.dataflow.bidi.ap.TaintMark
import org.opentaint.dataflow.bidi.ap.TypeFilter
import org.opentaint.dataflow.jvm.ap.ifds.JIRFactTypeChecker
import org.opentaint.dataflow.jvm.ap.ifds.taint.PrimitiveTaintExt
import org.opentaint.ir.api.jvm.JIRPrimitiveType
import org.opentaint.ir.api.jvm.JIRType
import org.opentaint.ir.api.jvm.ext.ifArrayGetElementType
import org.opentaint.ir.api.jvm.ext.unboxIfNeeded
import java.util.concurrent.ConcurrentHashMap

/** One shared path filter per type, with a primitive mark policy at each known element level. */
class JIRTypeFilters(private val checker: JIRFactTypeChecker, private val manager: ApManager) {
    private val byType = ConcurrentHashMap<JIRType, TypeFilter>()

    fun of(t: JIRType?): TypeFilter? = t?.let { byType.computeIfAbsent(it, ::make) }

    /** The root and first declaring type constrain the base; the final value type constrains the temporary. */
    fun forField(baseType: JIRType?, path: List<AccessorIdx>): Pair<TypeFilter?, TypeFilter?> {
        val accessors = path.map(manager.accessors::accessor)
        val root = of(baseType)
        val declaring = (accessors.firstOrNull() as? FieldAccessor)?.let { of(checker.fieldClassType(it)) }
        val base = when {
            root == null -> declaring
            declaring == null -> root
            else -> root.and(declaring)
        }
        return base to of(valueType(baseType, path))
    }

    /** A field supplies its declared type, including after a static prefix or an unknown element level. */
    fun valueType(baseType: JIRType?, path: List<AccessorIdx>): JIRType? {
        var type = baseType
        for (i in path) type = when (val a = manager.accessors.accessor(i)) {
            is FieldAccessor -> checker.fieldAccessorType(a)
            ElementAccessor -> type?.ifArrayGetElementType
            else -> null
        }
        return type
    }

    private fun make(t: JIRType): TypeFilter {
        val levels = generateSequence(t) { it.ifArrayGetElementType }.toList()
        val primitive = levels.map { it.typeName == "java.lang.Character" || it.unboxIfNeeded() is JIRPrimitiveType }
        // G6 drop form: a boxed level is a class (Integer, Character) with fields; a true primitive level has none.
        val boxed = levels.mapIndexed { k, type -> primitive[k] && type !is JIRPrimitiveType }
        return TypeFilter(checker.localFilter(t),
            markPolicy = if (true !in primitive) null
                else LevelMarkPolicy(primitive.toBooleanArray(), boxed.toBooleanArray(), ::isPrimitiveTracking))
    }

    fun isPrimitiveTracking(m: TaintMark): Boolean =
        manager.marks.name(m).endsWith(PrimitiveTaintExt.PRIMITIVE_TRACKING_ENABLED_MODE)
}
