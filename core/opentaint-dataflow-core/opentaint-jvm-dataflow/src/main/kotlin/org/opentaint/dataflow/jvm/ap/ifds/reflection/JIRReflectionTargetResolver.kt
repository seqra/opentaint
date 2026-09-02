package org.opentaint.dataflow.jvm.ap.ifds.reflection

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAllocInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasInfo
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.ir.api.jvm.JIRClassOrInterface
import org.opentaint.ir.api.jvm.JIRClassType
import org.opentaint.ir.api.jvm.JIRField
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRClassConstant
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRInstList
import org.opentaint.ir.api.jvm.cfg.JIRInstanceCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRLocalVar
import org.opentaint.ir.api.jvm.cfg.JIRStringConstant
import org.opentaint.ir.api.jvm.cfg.JIRValue
import org.opentaint.ir.api.jvm.ext.cfg.callExpr

class JIRReflectionTargetResolver {

    sealed interface Resolution {
        data object NotReflective : Resolution
        data object Failed : Resolution
        data class MethodTargets(val methods: List<JIRMethod>) : Resolution
        data class FieldTargets(val fields: List<JIRField>, val write: Boolean) : Resolution
    }

    fun resolveReflectiveTargets(
        call: JIRCallExpr,
        location: JIRInst,
        context: JIRMethodAnalysisContext
    ): Resolution {
        if (call !is JIRInstanceCallExpr) return Resolution.NotReflective

        val callee = call.method.method
        if (callee.name !in REFLECTIVE_ACCESSORS) return Resolution.NotReflective

        val enclosingClassName = callee.enclosingClass.name

        return when {
            enclosingClassName == REFLECT_METHOD && callee.name == INVOKE ->
                resolveInvocationTargets(call, location, context)

            enclosingClassName == REFLECT_FIELD && callee.name in FIELD_READ_METHODS ->
                resolveFieldTargets(call, location, context, write = false)

            enclosingClassName == REFLECT_FIELD && callee.name in FIELD_WRITE_METHODS ->
                resolveFieldTargets(call, location, context, write = true)

            else -> Resolution.NotReflective
        }
    }

    private fun resolveFieldTargets(
        call: JIRInstanceCallExpr,
        location: JIRInst,
        context: JIRMethodAnalysisContext,
        write: Boolean
    ): Resolution {
        val instList = (location.location.method as? JIRMethod)?.instList ?: return Resolution.Failed
        val aliasAnalysis = context.aliasAnalysis ?: return Resolution.Failed

        val lookups = memberLookupCalls(
            call.instance, location, aliasAnalysis, instList,
            declaredName = GET_DECLARED_FIELD, inheritedName = GET_FIELD
        )
        if (lookups.isEmpty()) return Resolution.Failed

        val targets = LinkedHashSet<JIRField>()
        for (lookup in lookups) {
            val declaringClasses = classConstants(lookup.call.instance, lookup.statement, aliasAnalysis, instList)
            if (declaringClasses.isEmpty()) return Resolution.Failed

            val nameArgument = lookup.call.args.firstOrNull() ?: return Resolution.Failed
            val names = stringConstants(nameArgument, lookup.statement, aliasAnalysis, instList)
            if (names.isEmpty()) return Resolution.Failed

            for (declaringClass in declaringClasses) {
                for (name in names) {
                    targets += fieldTargets(declaringClass, name, lookup.declaredOnly)
                }
            }
        }

        if (targets.isEmpty()) return Resolution.Failed

        return Resolution.FieldTargets(targets.toList(), write)
    }

    private fun resolveInvocationTargets(
        call: JIRInstanceCallExpr,
        location: JIRInst,
        context: JIRMethodAnalysisContext
    ): Resolution {
        val instList = (location.location.method as? JIRMethod)?.instList ?: return Resolution.Failed
        val aliasAnalysis = context.aliasAnalysis ?: return Resolution.Failed

        val lookups = memberLookupCalls(
            call.instance, location, aliasAnalysis, instList,
            declaredName = GET_DECLARED_METHOD, inheritedName = GET_METHOD
        )
        if (lookups.isEmpty()) return Resolution.Failed

        val targets = LinkedHashSet<JIRMethod>()
        for (lookup in lookups) {
            val declaringClasses = classConstants(lookup.call.instance, lookup.statement, aliasAnalysis, instList)
            if (declaringClasses.isEmpty()) return Resolution.Failed

            val nameArgument = lookup.call.args.firstOrNull() ?: return Resolution.Failed
            val names = stringConstants(nameArgument, lookup.statement, aliasAnalysis, instList)
            if (names.isEmpty()) return Resolution.Failed

            for (declaringClass in declaringClasses) {
                for (name in names) {
                    targets += methodTargets(declaringClass, name, lookup.declaredOnly)
                }
            }
        }

        if (targets.isEmpty()) return Resolution.Failed

        return Resolution.MethodTargets(targets.toList())
    }

    private data class MemberLookup(
        val call: JIRInstanceCallExpr,
        val statement: JIRInst,
        val declaredOnly: Boolean
    )

    private fun memberLookupCalls(
        memberObject: JIRValue,
        location: JIRInst,
        aliasAnalysis: JIRLocalAliasAnalysis,
        instList: JIRInstList<JIRInst>,
        declaredName: String,
        inheritedName: String
    ): List<MemberLookup> {
        val aliases = aliasesOf(memberObject, location, aliasAnalysis) ?: return emptyList()

        val result = mutableListOf<MemberLookup>()
        for (statement in allocStatements(aliases, instList, memberObject)) {
            val lookupCall = statement.callExpr as? JIRInstanceCallExpr ?: continue

            val lookupMethod = lookupCall.method.method
            if (lookupMethod.enclosingClass.name != JAVA_LANG_CLASS) continue

            val declaredOnly = when (lookupMethod.name) {
                declaredName -> true
                inheritedName -> false
                else -> continue
            }

            result += MemberLookup(lookupCall, statement, declaredOnly)
        }

        return result
    }

    private fun stringConstants(
        value: JIRValue,
        location: JIRInst,
        aliasAnalysis: JIRLocalAliasAnalysis,
        instList: JIRInstList<JIRInst>
    ): List<String> {
        if (value is JIRStringConstant) return listOf(value.value)

        val aliases = aliasesOf(value, location, aliasAnalysis) ?: return emptyList()

        val result = mutableListOf<String>()

        for (alias in aliases.filterIsInstance<AliasApInfo>()) {
            if (alias.accessors.isNotEmpty()) continue
            val base = alias.base as? AccessPathBase.Constant ?: continue
            if (base.typeName != JAVA_LANG_STRING) continue
            result += base.value
        }

        for (statement in allocStatements(aliases, instList, value)) {
            val constant = (statement as? JIRAssignInst)?.rhv as? JIRStringConstant ?: continue
            result += constant.value
        }

        return result
    }

    private fun classConstants(
        value: JIRValue,
        location: JIRInst,
        aliasAnalysis: JIRLocalAliasAnalysis,
        instList: JIRInstList<JIRInst>
    ): List<JIRClassOrInterface> {
        if (value is JIRClassConstant) return listOfNotNull(value.declaringClass())

        val aliases = aliasesOf(value, location, aliasAnalysis) ?: return emptyList()

        val result = mutableListOf<JIRClassOrInterface>()
        for (statement in allocStatements(aliases, instList, value)) {
            val constant = (statement as? JIRAssignInst)?.rhv as? JIRClassConstant ?: continue
            result += constant.declaringClass() ?: continue
        }

        return result
    }

    private fun JIRClassConstant.declaringClass(): JIRClassOrInterface? = (klass as? JIRClassType)?.jIRClass

    private fun aliasesOf(
        value: JIRValue,
        location: JIRInst,
        aliasAnalysis: JIRLocalAliasAnalysis
    ): List<AliasInfo>? {
        if (value !is JIRLocalVar) return null
        return aliasAnalysis.findAlias(AccessPathBase.LocalVar(value.index), location)
    }

    private fun allocStatements(
        aliases: List<AliasInfo>,
        instList: JIRInstList<JIRInst>,
        queried: JIRValue
    ): List<JIRInst> {
        val allocations = aliases
            .filterIsInstance<AliasAllocInfo>()
            .mapNotNull { instList.getOrNull(it.allocInst) }

        val definitions = allocations.filter { (it as? JIRAssignInst)?.lhv == queried }

        return definitions.ifEmpty { allocations }
    }

    private fun fieldTargets(
        declaringClass: JIRClassOrInterface,
        name: String,
        declaredOnly: Boolean
    ): List<JIRField> {
        if (declaredOnly) {
            return declaringClass.declaredFields.filter { it.name == name }
        }

        val result = mutableListOf<JIRField>()
        val visited = hashSetOf<String>()
        var current: JIRClassOrInterface? = declaringClass
        while (current != null && visited.add(current.name)) {
            current.declaredFields.filterTo(result) { it.name == name && it.isPublic }
            current = current.superClass
        }

        return result
    }

    private fun methodTargets(
        declaringClass: JIRClassOrInterface,
        name: String,
        declaredOnly: Boolean
    ): List<JIRMethod> {
        if (declaredOnly) {
            return declaringClass.declaredMethods.filter { it.name == name && !it.isConstructor }
        }

        val result = mutableListOf<JIRMethod>()
        val visited = hashSetOf<String>()
        var current: JIRClassOrInterface? = declaringClass
        while (current != null && visited.add(current.name)) {
            current.declaredMethods.filterTo(result) { it.name == name && !it.isConstructor && it.isPublic }
            current = current.superClass
        }

        return result
    }

    private companion object {
        const val REFLECT_METHOD = "java.lang.reflect.Method"
        const val REFLECT_FIELD = "java.lang.reflect.Field"
        const val GET_FIELD = "getField"
        const val GET_DECLARED_FIELD = "getDeclaredField"

        val FIELD_READ_METHODS = setOf(
            "get", "getBoolean", "getByte", "getChar", "getDouble", "getFloat", "getInt", "getLong", "getShort"
        )

        val FIELD_WRITE_METHODS = setOf(
            "set", "setBoolean", "setByte", "setChar", "setDouble", "setFloat", "setInt", "setLong", "setShort"
        )

        val REFLECTIVE_ACCESSORS: Set<String> = FIELD_READ_METHODS + FIELD_WRITE_METHODS + INVOKE
        const val JAVA_LANG_CLASS = "java.lang.Class"
        const val JAVA_LANG_STRING = "java.lang.String"
        const val INVOKE = "invoke"
        const val GET_METHOD = "getMethod"
        const val GET_DECLARED_METHOD = "getDeclaredMethod"
    }
}
