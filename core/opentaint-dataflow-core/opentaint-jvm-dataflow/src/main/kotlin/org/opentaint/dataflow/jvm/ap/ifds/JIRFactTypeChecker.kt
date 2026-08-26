package org.opentaint.dataflow.jvm.ap.ifds

import it.unimi.dsi.fastutil.longs.LongLongImmutablePair
import it.unimi.dsi.fastutil.longs.LongLongPair
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FactTypeChecker.AlwaysAcceptFilter
import org.opentaint.dataflow.ap.ifds.FactTypeChecker.CompatibilityFilterResult
import org.opentaint.dataflow.ap.ifds.FactTypeChecker.FactApFilter
import org.opentaint.dataflow.ap.ifds.FactTypeChecker.FilterResult
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoGroupAccessor
import org.opentaint.dataflow.ap.ifds.ValueAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.jvm.ap.ifds.taint.PrimitiveTaintExt
import org.opentaint.dataflow.jvm.util.JIRHierarchyInfo
import org.opentaint.ir.api.common.CommonType
import org.opentaint.ir.api.jvm.JIRArrayType
import org.opentaint.ir.api.jvm.JIRBoundedWildcard
import org.opentaint.ir.api.jvm.JIRClassOrInterface
import org.opentaint.ir.api.jvm.JIRClassType
import org.opentaint.ir.api.jvm.JIRClasspath
import org.opentaint.ir.api.jvm.JIRPrimitiveType
import org.opentaint.ir.api.jvm.JIRRefType
import org.opentaint.ir.api.jvm.JIRType
import org.opentaint.ir.api.jvm.JIRTypeVariable
import org.opentaint.ir.api.jvm.JIRUnboundWildcard
import org.opentaint.ir.api.jvm.ext.ifArrayGetElementType
import org.opentaint.ir.api.jvm.ext.isAssignable
import org.opentaint.ir.api.jvm.ext.isSubClassOf
import org.opentaint.ir.api.jvm.ext.objectType
import org.opentaint.ir.api.jvm.ext.unboxIfNeeded
import org.opentaint.ir.impl.features.classpaths.JIRUnknownType
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.LongAdder

class JIRFactTypeChecker(private val cp: JIRClasspath) : FactTypeChecker {
    private val hierarchyInfo = JIRHierarchyInfo(cp)

    private val objectType by lazy { cp.objectType }
    private val objectClass by lazy { objectType.jIRClass }

    val localFactsTotal = LongAdder()
    val localFactsRejected = LongAdder()

    private fun Boolean.logLocalFactCheck(): Boolean = also { isCorrect ->
        localFactsTotal.increment()
        if (!isCorrect) localFactsRejected.increment()
    }

    val accessTotal = LongAdder()
    val accessRejected = LongAdder()

    private fun Boolean.logAccessCheck(): Boolean = also { isCorrect ->
        accessTotal.increment()
        if (!isCorrect) accessRejected.increment()
    }

    /**
     * Why a FIELD step through the ACCESS filter was allowed, split by whether the type system
     * actually said anything.
     *
     * The filter is the only thing that stops one field following another that could never follow
     * it, so "how often does it reject" is not the interesting number -- "how often does it accept
     * because it had nothing to say" is. A step is [fieldAcceptVacuousObject] when the type at the
     * current position is `java.lang.Object` (or an unresolvable/variable type), which admits every
     * field in the program; [fieldAcceptVacuousInterface] when it is an interface, where
     * `interfaceMayHaveSubtypeOf` admits any class that could implement it; and
     * [fieldAcceptTyped] only when a real class-to-class relation was checked and held.
     */
    val fieldAcceptTyped = LongAdder()
    val fieldAcceptVacuousObject = LongAdder()
    val fieldAcceptVacuousTypeVar = LongAdder()
    val fieldAcceptVacuousInterface = LongAdder()
    val fieldAcceptUnknownField = LongAdder()
    val fieldRejectTyped = LongAdder()
    val fieldRejectNotRef = LongAdder()

    /**
     * Access-filter rejections split by the accessor that was refused.
     *
     * The engine-wide `access R/T` line says 96% of everything is rejected but not WHAT: a field
     * that cannot follow this type is a real pruning of the object graph, while a `[value]` refused
     * on a reference is a step the generator should never have proposed. The two call for different
     * fixes, so they are counted apart.
     */
    val rejectByField = LongAdder()
    val rejectByElement = LongAdder()
    val rejectByValue = LongAdder()
    val rejectByAny = LongAdder()
    val rejectByMark = LongAdder()
    val acceptOther = LongAdder()

    /**
     * The (type at the position -> field) pairs the filter waves through without being able to
     * check them, most frequent first.
     *
     * This is the table that names WHERE the type system stops constraining the walk. Bounded at
     * [VACUOUS_SITE_LIMIT] distinct keys so a pathological program cannot turn a diagnostic into a
     * leak; once full it keeps counting the keys it already has.
     */
    val vacuousAcceptSites = ConcurrentHashMap<String, LongAdder>()

    val compatibilityTotal = LongAdder()
    val compatibilityRejected = LongAdder()

    private fun Boolean.logCompatibilityCheck(): Boolean = also { isCorrect ->
        compatibilityTotal.increment()
        if (!isCorrect) compatibilityRejected.increment()
    }

    private inner class AccessorFilter(
        private val actualType: JIRType,
        private val isLocalCheck: Boolean
    ) : FactApFilter {
        override fun check(accessor: Accessor): FilterResult = checkAccessor(accessor).also {
            val result = it !== FilterResult.Reject
            if (isLocalCheck) result.logLocalFactCheck() else result.logAccessCheck()
        }

        private fun checkAccessor(accessor: Accessor): FilterResult {
            when (accessor) {
                is FinalAccessor, is ClassStaticAccessor -> {
                    if (!isLocalCheck) acceptOther.increment()
                    return FilterResult.Accept
                }

                is AnyAccessor -> {
                    if (actualType.unboxIfNeeded() is JIRPrimitiveType) {
                        if (!isLocalCheck) rejectByAny.increment()
                        return FilterResult.Reject
                    }

                    if (!isLocalCheck) acceptOther.increment()
                    return FilterResult.Accept
                }

                is TaintMarkAccessor -> {
                    if (actualType.unboxIfNeeded() is JIRPrimitiveType) {
                        if (!accessor.mark.endsWith(PrimitiveTaintExt.PRIMITIVE_TRACKING_ENABLED_MODE)) {
                            if (!isLocalCheck) rejectByMark.increment()
                            return FilterResult.Reject
                        }
                    }

                    if (!isLocalCheck) acceptOther.increment()
                    return FilterResult.Accept
                }

                is FieldAccessor -> {
                    if (actualType !is JIRRefType) {
                        if (!isLocalCheck) {
                            fieldRejectNotRef.increment()
                            rejectByField.increment()
                        }
                        return FilterResult.Reject
                    }

                    val factType = fieldClassType(accessor)
                    if (factType == null) {
                        if (!isLocalCheck) fieldAcceptUnknownField.increment()
                        return FilterResult.Accept
                    }
                    if (!typeMayHaveSubtypeOf(actualType, factType)) {
                        if (!isLocalCheck) {
                            fieldRejectTyped.increment()
                            rejectByField.increment()
                        }
                        return FilterResult.Reject
                    }
                    val vacuous = classifyFieldAccept(actualType, accessor, count = !isLocalCheck)
                    // MEASUREMENT ONLY, and unsound: refuse the steps the type system could not
                    // justify, to put an upper bound on what constraining them could ever buy and a
                    // lower bound on what it would cost in findings. A real fix widens such a
                    // position instead of cutting it -- see the anatomy document, section 8.
                    if (vacuous != Vacuity.NONE && rejectVacuous(vacuous)) return FilterResult.Reject
                    return FilterResult.Accept
                }

                ElementAccessor -> {
                    if (actualType !is JIRRefType) {
                        if (!isLocalCheck) rejectByElement.increment()
                        return FilterResult.Reject
                    }
                    if (!typeMayBeArrayType(actualType)) {
                        if (!isLocalCheck) rejectByElement.increment()
                        return FilterResult.Reject
                    }

                    val actualElementType = actualType.ifArrayGetElementType
                    if (actualElementType == null) {
                        if (!isLocalCheck) acceptOther.increment()
                        return FilterResult.Accept
                    }

                    return FilterResult.FilterNext(
                        AccessorFilter(actualElementType, isLocalCheck)
                    )
                }

                ValueAccessor -> {
                    return if (actualType is JIRPrimitiveType) {
                        if (!isLocalCheck) acceptOther.increment()
                        FilterResult.Accept
                    } else {
                        if (!isLocalCheck) rejectByValue.increment()
                        FilterResult.Reject
                    }
                }

                is TypeInfoAccessor -> {
                    if (!isLocalCheck) acceptOther.increment()
                    return FilterResult.Accept
                }
                TypeInfoGroupAccessor -> {
                    if (!isLocalCheck) acceptOther.increment()
                    return FilterResult.Accept
                }
            }
        }

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false

            other as AccessorFilter

            if (isLocalCheck != other.isLocalCheck) return false
            if (actualType != other.actualType) return false

            return true
        }

        override fun hashCode(): Int {
            var result = isLocalCheck.hashCode()
            result = 31 * result + actualType.hashCode()
            return result
        }
    }

    /**
     * Which arm of [typeMayHaveSubtypeOf] said yes.
     *
     * `java.lang.Object` and a type variable admit everything; an interface admits every class that
     * could implement it, which on a Spring project is most of them. Only the remaining arm is a
     * check that could have failed.
     */
    /**
     * Why a field step was allowed: which arm of the check had nothing to say.
     *
     * [OBJECT] and [TYPE_VAR] are positions with no nominal type at all -- `java.lang.Object`, a
     * type variable, a wildcard -- and admit every field in the program. [INTERFACE] admits every
     * field of every class that could implement it, which is weaker but still very wide on a Spring
     * project. [NONE] is a check that could have failed and did not.
     */
    enum class Vacuity { NONE, OBJECT, TYPE_VAR, INTERFACE }

    private fun classifyFieldAccept(actualType: JIRRefType, accessor: FieldAccessor, count: Boolean): Vacuity {
        val vacuity = vacuityOf(actualType)
        if (!count) return vacuity

        when (vacuity) {
            Vacuity.OBJECT -> fieldAcceptVacuousObject.increment()
            Vacuity.TYPE_VAR -> fieldAcceptVacuousTypeVar.increment()
            Vacuity.INTERFACE -> fieldAcceptVacuousInterface.increment()
            Vacuity.NONE -> {
                fieldAcceptTyped.increment()
                return vacuity
            }
        }

        val key = "$actualType -> ${accessor.className}#${accessor.fieldName}"
        val counter = vacuousAcceptSites[key]
        if (counter != null) {
            counter.increment()
            return vacuity
        }
        if (vacuousAcceptSites.size >= VACUOUS_SITE_LIMIT) return vacuity
        vacuousAcceptSites.computeIfAbsent(key) { LongAdder() }.increment()
        return vacuity
    }

    private fun vacuityOf(actualType: JIRRefType): Vacuity = when {
        actualType is JIRClassType && actualType == objectType -> Vacuity.OBJECT
        actualType is JIRClassType && actualType.jIRClass.isInterface -> Vacuity.INTERFACE
        // A type variable, a wildcard, or anything else that is neither a class nor an array: the
        // position has no nominal type, which is what a container's element or value accessor
        // leaves behind after erasure.
        actualType !is JIRClassType && actualType !is JIRArrayType -> Vacuity.TYPE_VAR
        else -> Vacuity.NONE
    }

    /** Top [topN] positions where the type system had nothing to say, and how often. */
    fun vacuousAcceptReport(topN: Int): String = vacuousAcceptSites.entries
        .sortedByDescending { it.value.sum() }
        .take(topN)
        .joinToString("\n") { "  ${it.value.sum()} | ${it.key}" }

    private inner class AccessorCompatibilityFilter(
        private val actualType: JIRType
    ) : FactTypeChecker.FactCompatibilityFilter {
        override fun check(accessor: Accessor): CompatibilityFilterResult  = checkAccessor(accessor).also {
            val result = it !== CompatibilityFilterResult.NotCompatible
            result.logCompatibilityCheck()
        }

        private fun checkAccessor(accessor: Accessor): CompatibilityFilterResult {
            if (accessor !is FieldAccessor) return CompatibilityFilterResult.Compatible

            val fieldType = fieldAccessorType(accessor)
                ?: return CompatibilityFilterResult.Compatible

            if (!typesCompatible(actualType, fieldType)) return CompatibilityFilterResult.NotCompatible

            return CompatibilityFilterResult.Compatible
        }
    }

    override fun filterFactByLocalType(actualType: CommonType?, factAp: FinalFactAp): FinalFactAp? {
        if (actualType == null) return factAp
        jIRDowncast<JIRType>(actualType)

        val filter = AccessorFilter(actualType, isLocalCheck = true)
        return factAp.filterFact(filter)
    }

    override fun accessPathFilter(accessPath: List<Accessor>): FactApFilter {
        val actualType = accessorActualType(accessPath) ?: return AlwaysAcceptFilter
        return AccessorFilter(actualType, isLocalCheck = false)
    }

    override fun accessPathCompatibilityFilter(accessPath: List<Accessor>): FactTypeChecker.FactCompatibilityFilter {
        val actualType = accessorActualType(accessPath) ?: return FactTypeChecker.AlwaysCompatibleFilter
        return AccessorCompatibilityFilter(actualType)
    }

    private fun accessorActualType(accessPath: List<Accessor>): JIRType? {
        val accessor = accessPath.lastOrNull() ?: return null
        return when (accessor) {
            is FieldAccessor -> fieldAccessorType(accessor)
            ElementAccessor -> {
                val prevAccessors = accessPath.subList(0, accessPath.size - 1)
                accessorActualType(prevAccessors)?.ifArrayGetElementType
            }
            ValueAccessor -> {
                val prevAccessors = accessPath.subList(0, accessPath.size - 1)
                accessorActualType(prevAccessors)
            }

            is TaintMarkAccessor, FinalAccessor, AnyAccessor, is ClassStaticAccessor -> null
            is TypeInfoAccessor, TypeInfoGroupAccessor -> null
        }
    }

    private fun fieldAccessorType(accessor: FieldAccessor): JIRType? {
        return cp.findTypeOrNull(accessor.fieldType)
    }

    private fun fieldClassType(accessor: FieldAccessor): JIRClassType? {
        return cp.findTypeOrNull(accessor.className) as? JIRClassType
    }

    private fun typeMayBeArrayType(type: JIRRefType): Boolean = when (type) {
        is JIRArrayType -> true
        is JIRClassType -> type == objectType
        is JIRTypeVariable -> type.bounds.all { bound -> typeMayBeArrayType(bound) }

        // todo: check wildcards
        is JIRUnboundWildcard, is JIRBoundedWildcard -> true

        else -> error("Unexpected type: $type")
    }

    private fun typesCompatible(t1: JIRType, t2: JIRType): Boolean {
        if (t1 == t2) return true
        if (t1 is JIRUnknownType || t2 is JIRUnknownType) return true
        if (t1.isAssignable(t2) || t2.isAssignable(t1)) return true
        if (t1 !is JIRRefType || t2 !is JIRRefType) return false
        if (t1 !is JIRClassType && t2 !is JIRClassType) return true
        if (t1 is JIRClassType && typeMayHaveSubtypeOf(t2, t1)) return true
        if (t2 is JIRClassType && typeMayHaveSubtypeOf(t1, t2)) return true
        return false
    }

    private fun typeMayHaveSubtypeOf(type: JIRRefType, requiredType: JIRClassType): Boolean = when (type) {
        is JIRClassType -> if (type.jIRClass.isInterface) {
            interfaceMayHaveSubtypeOf(type.jIRClass, requiredType.jIRClass)
        } else {
            requiredType.isAssignable(type) || type.isAssignable(requiredType)
        }

        is JIRArrayType -> requiredType.isAssignable(type)
        is JIRTypeVariable -> type.bounds.all { bound -> typeMayHaveSubtypeOf(bound, requiredType) }

        // todo: check wildcards
        is JIRUnboundWildcard, is JIRBoundedWildcard -> true

        else -> error("Unexpected type: $type")
    }

    private fun rejectVacuous(vacuity: Vacuity): Boolean = when (REJECT_VACUOUS_MODE) {
        "all", "true" -> true
        "object" -> vacuity == Vacuity.OBJECT || vacuity == Vacuity.TYPE_VAR
        "interface" -> vacuity == Vacuity.INTERFACE
        else -> false
    }

    // todo: cache limit?
    private val typeMayHaveSubtypeOfCache = ConcurrentHashMap<LongLongPair, Boolean>()

    companion object {
        /** Distinct (type, field) keys the vacuous-accept table will hold before it stops growing. */
        const val VACUOUS_SITE_LIMIT = 20_000

        /**
         * Refuse the field steps the type system could not justify.
         *
         * `-Dopentaint.rejectVacuousFieldSteps=<mode>`, where mode is `object` (only positions with
         * no nominal type), `interface`, or `all`. An ablation, not a fix: it is unsound, it loses
         * every flow that passes through a container or an `Object`-typed field, and it is here to
         * bound the size of the prize. A real fix WIDENS such a position instead of cutting it.
         */
        val REJECT_VACUOUS_MODE: String =
            System.getProperty("opentaint.rejectVacuousFieldSteps")?.trim()?.lowercase().orEmpty()
    }

    fun typeMayHaveSubtypeOf(typeName: String, requiredTypeName: String): Boolean {
        if (requiredTypeName == "java.lang.Object") return true
        if (typeName == "java.lang.Object") return true

        if (typeName.endsWith("[]")) {
            return requiredTypeName.endsWith("[]")
        }

        if (requiredTypeName.endsWith("[]")) {
            return false
        }

        val typeNameId = hierarchyInfo.persistence.findSymbolId(typeName)
        val requiredTypeNameId = hierarchyInfo.persistence.findSymbolId(requiredTypeName)

        val cacheKey = LongLongImmutablePair(typeNameId, requiredTypeNameId)
        return typeMayHaveSubtypeOfCache.computeIfAbsent(cacheKey) {
            computeTypeMayHaveSubtypeOf(typeName, requiredTypeName)
        }
    }

    private fun computeTypeMayHaveSubtypeOf(
        typeName: String, requiredTypeName: String
    ): Boolean {
        val typeCls = cp.findClassOrNull(typeName) ?: return true
        val requiredTypeCls = cp.findClassOrNull(requiredTypeName) ?: return true

        return if (typeCls.isInterface) {
            interfaceMayHaveSubtypeOf(typeCls, requiredTypeCls)
        } else {
            typeCls.isSubClassOf(requiredTypeCls) || requiredTypeCls.isSubClassOf(typeCls)
        }
    }

    // todo: cache limit?
    private val interfaceMayHaveSubtypeOfCache = ConcurrentHashMap<LongLongPair, Boolean>()

    private fun interfaceMayHaveSubtypeOf(
        interfaceType: JIRClassOrInterface,
        requiredType: JIRClassOrInterface
    ): Boolean {
        if (requiredType == objectClass) return true

        val requiredTypeId = hierarchyInfo.persistence.findSymbolId(requiredType.name)
        val interfaceTypeId = hierarchyInfo.persistence.findSymbolId(interfaceType.name)

        val cacheKey = LongLongImmutablePair(requiredTypeId, interfaceTypeId)
        return interfaceMayHaveSubtypeOfCache.computeIfAbsent(cacheKey) {
            computeInterfaceMayHaveSubtypeOf(requiredType, interfaceType, requiredTypeId)
        }
    }

    private fun computeInterfaceMayHaveSubtypeOf(
        requiredType: JIRClassOrInterface,
        interfaceType: JIRClassOrInterface,
        requiredTypeId: Long
    ): Boolean {
        val subClassCheckCache = hashSetOf<JIRClassOrInterface>()
        if (isSubClassOfInterface(requiredType, interfaceType, subClassCheckCache)) return true

        if (requiredType.isFinal) return false

        hierarchyInfo.forEachSubClassName(requiredTypeId) { className ->
            val cls = cp.findClassOrNull(className) ?: return true
            if (isSubClassOfInterface(cls, interfaceType, subClassCheckCache)) return true
        }

        return false
    }

    private fun isSubClassOfInterface(
        currentCls: JIRClassOrInterface,
        interfaceType: JIRClassOrInterface,
        checkedTypes: MutableSet<JIRClassOrInterface>
    ): Boolean {
        val uncheckedClasses = mutableListOf(currentCls)
        while (uncheckedClasses.isNotEmpty()) {
            val cls = uncheckedClasses.removeLast()
            if (cls == interfaceType) return true

            if (!checkedTypes.add(cls)) continue

            cls.superClass?.let { uncheckedClasses.add(it) }

            uncheckedClasses.addAll(cls.interfaces)
        }
        return false
    }
}
