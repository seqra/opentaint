package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.jvm.util.JIRHierarchyInfo
import org.opentaint.ir.api.jvm.JIRArrayType
import org.opentaint.ir.api.jvm.JIRClassOrInterface
import org.opentaint.ir.api.jvm.JIRClassType
import org.opentaint.ir.api.jvm.JIRClasspath
import org.opentaint.ir.api.jvm.JIRType
import java.util.concurrent.ConcurrentHashMap

class JIRBackwardStarUnroller(private val cp: JIRClasspath) {
    private class Unrolling(val accessors: List<Accessor>?)

    private val hierarchy by lazy { JIRHierarchyInfo(cp) }
    private val classAccessors = ConcurrentHashMap<String, Unrolling>()

    fun unroll(fact: FinalFactAp, type: JIRType?): List<FinalFactAp>? {
        if (!fact.startsWithAccessor(AnyAccessor)) return null
        val star = fact.readAccessor(AnyAccessor) ?: return null
        val accessors = type?.let { starAccessors(it) } ?: return null

        return buildList {
            fact.clearAccessor(AnyAccessor)?.let(::add)
            star.clearAccessor(AnyAccessor)?.let(::add)
            for (accessor in accessors) {
                fact.readAccessor(accessor)?.prependAccessor(accessor)?.let(::add)
            }
        }
    }

    private fun starAccessors(type: JIRType): List<Accessor>? = when (type) {
        is JIRArrayType -> listOf(ElementAccessor)
        is JIRClassType -> classAccessors.computeIfAbsent(type.jIRClass.name) {
            Unrolling(fieldAccessors(type.jIRClass))
        }.accessors

        else -> null
    }

    private fun fieldAccessors(cls: JIRClassOrInterface): List<Accessor>? {
        if (cls.isInterface || cls.name == JAVA_LANG_OBJECT) return null

        val accessors = linkedSetOf<Accessor>()
        var current: JIRClassOrInterface? = cls
        while (current != null) {
            addDeclaredFields(current, accessors)
            current = current.superClass
        }

        hierarchy.forEachSubClassName(cls.name) { subClassName ->
            val subClass = cp.findClassOrNull(subClassName) ?: return null
            addDeclaredFields(subClass, accessors)
        }

        return accessors.toList()
    }

    private fun addDeclaredFields(cls: JIRClassOrInterface, accessors: MutableSet<Accessor>) {
        for (field in cls.declaredFields) {
            if (field.isStatic) continue
            accessors += FieldAccessor(cls.name, field.name, field.type.typeName)
        }
    }

    companion object {
        private const val JAVA_LANG_OBJECT = "java.lang.Object"
    }
}
