package org.opentaint.dataflow.jvm.ap.ifds.reflection

import org.opentaint.dataflow.jvm.util.JIRInstListBuilder
import org.opentaint.ir.api.jvm.JIRClassOrInterface
import org.opentaint.ir.api.jvm.JIRClassType
import org.opentaint.ir.api.jvm.JIRClasspath
import org.opentaint.ir.api.jvm.JIRClasspathExtFeature
import org.opentaint.ir.api.jvm.JIRClasspathExtFeature.JIRResolvedClassResult
import org.opentaint.ir.api.jvm.JIRField
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.JIRRefType
import org.opentaint.ir.api.jvm.JIRType
import org.opentaint.ir.api.jvm.cfg.JIRArgument
import org.opentaint.ir.api.jvm.cfg.JIRArrayAccess
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRBool
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRCallInst
import org.opentaint.ir.api.jvm.cfg.JIRCastExpr
import org.opentaint.ir.api.jvm.cfg.JIREqExpr
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRIfInst
import org.opentaint.ir.api.jvm.cfg.JIRInstRef
import org.opentaint.ir.api.jvm.cfg.JIRInt
import org.opentaint.ir.api.jvm.cfg.JIRLocalVar
import org.opentaint.ir.api.jvm.cfg.JIRNullConstant
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.cfg.JIRStaticCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRValue
import org.opentaint.ir.api.jvm.cfg.JIRVirtualCallExpr
import org.opentaint.ir.api.jvm.ext.boolean
import org.opentaint.ir.api.jvm.ext.int
import org.opentaint.ir.api.jvm.ext.objectType
import org.opentaint.ir.api.jvm.ext.toType
import org.opentaint.ir.impl.cfg.TypedStaticMethodRefImpl
import org.opentaint.ir.impl.cfg.VirtualMethodRefImpl
import org.opentaint.ir.impl.features.classpaths.AbstractJIRResolvedResult.JIRResolvedClassResultImpl
import org.opentaint.ir.impl.features.classpaths.JIRUnknownType
import org.opentaint.ir.impl.features.classpaths.VirtualLocation
import org.opentaint.ir.impl.features.classpaths.virtual.JIRVirtualMethod
import org.opentaint.ir.impl.features.classpaths.virtual.JIRVirtualParameter
import org.opentaint.ir.impl.types.JIRTypedFieldImpl
import org.opentaint.ir.impl.types.substition.JIRSubstitutorImpl
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger

class JIRReflectionProxyFeature : JIRClasspathExtFeature {

    private val proxyClasses = ConcurrentHashMap<String, JIRReflectionProxyClass>()
    private val proxies = ConcurrentHashMap<ProxyKey, JIRReflectionProxyMethod>()
    private val proxyIndex = AtomicInteger()

    override fun tryFindClass(classpath: JIRClasspath, name: String): JIRResolvedClassResult? {
        val cls = proxyClasses[name] ?: return null
        return JIRResolvedClassResultImpl(name, cls)
    }

    fun methodProxy(cp: JIRClasspath, accessor: JIRMethod, targets: List<JIRMethod>): JIRMethod? {
        val owner = targets.firstOrNull()?.enclosingClass ?: return null
        val signatures = targets.map { "${it.enclosingClass.name}#${it.name}${it.description}" }.sorted()
        val key = ProxyKey(owner.name, accessor.name, signatures)

        return buildOrReuse(cp, owner, accessor, key, targets) { ctx ->
            for (target in targets) ctx.dispatchBranch { emitInvocation(cp, ctx, target) }
        }
    }

    fun fieldProxy(cp: JIRClasspath, accessor: JIRMethod, targets: List<JIRField>, write: Boolean): JIRMethod? {
        val owner = targets.firstOrNull()?.enclosingClass ?: return null
        val signatures = targets.map { "${it.enclosingClass.name}#${it.name}" }.sorted()
        val key = ProxyKey(owner.name, accessor.name, signatures)

        return buildOrReuse(cp, owner, accessor, key, emptyList()) { ctx ->
            for (target in targets) {
                ctx.dispatchBranch {
                    if (write) emitFieldWrite(cp, ctx, target) else emitFieldRead(cp, ctx, target)
                }
            }
        }
    }

    private fun buildOrReuse(
        cp: JIRClasspath,
        owner: JIRClassOrInterface,
        accessor: JIRMethod,
        key: ProxyKey,
        targets: List<JIRMethod>,
        emitBody: (ProxyBodyContext) -> Unit
    ): JIRMethod = proxies.computeIfAbsent(key) {
        val className = "${owner.name}\$\$jIR_reflection_proxy"
        val proxyClass = proxyClasses.computeIfAbsent(className) {
            JIRReflectionProxyClass(className)
                .also { cls -> cls.bindWithLocation(cp, owner.declaration.location) }
        }

        val instructions = JIRInstListBuilder()
        val method = JIRReflectionProxyMethod(
            name = "${accessor.name}$${proxyIndex.getAndIncrement()}",
            returnType = accessor.returnType,
            description = accessor.description,
            parameters = accessor.parameters.map { JIRVirtualParameter(it.index, it.type) },
            targets = targets,
            instructions = instructions
        ).also { it.bind(proxyClass) }

        proxyClass.addProxyMethod(method as JIRVirtualMethod)

        val returnType = cp.findTypeOrNull(accessor.returnType.typeName)
        val result = returnType?.let { type ->
            instructions.local("%result", type).also { local ->
                if (type is JIRRefType) {
                    instructions.addInstWithLocation(method) { loc -> JIRAssignInst(loc, local, JIRNullConstant(type)) }
                }
            }
        }

        val ctx = ProxyBodyContext(cp, method, instructions, accessor, result)
        emitBody(ctx)

        instructions.addInstWithLocation(method) { loc -> JIRReturnInst(loc, result) }

        method
    }

    private class ProxyBodyContext(
        val cp: JIRClasspath,
        val method: JIRReflectionProxyMethod,
        val instructions: JIRInstListBuilder,
        val accessor: JIRMethod,
        val result: JIRLocalVar?
    ) {
        fun parameter(index: Int): JIRValue {
            val declared = accessor.parameters[index].type.typeName
            val type = cp.findTypeOrNull(declared) ?: cp.objectType
            return JIRArgument(index, "arg$index", type)
        }

        fun local(name: String, type: JIRType) = instructions.local(name, type)

        fun add(build: (org.opentaint.ir.api.jvm.cfg.JIRInstLocation) -> org.opentaint.ir.api.jvm.cfg.JIRInst) {
            instructions.addInstWithLocation(method, build)
        }

        inline fun dispatchBranch(body: () -> Unit) {
            val condition = local("%dispatch", cp.boolean)
            add { loc -> JIRAssignInst(loc, condition, nonDeterministicChoice(cp)) }

            var branchIdx = -1
            add { loc ->
                branchIdx = loc.index
                JIRIfInst(
                    loc,
                    condition = JIREqExpr(cp.boolean, condition, JIRBool(true, cp.boolean)),
                    trueBranch = JIRInstRef(loc.index + 1),
                    falseBranch = JIRInstRef(loc.index + 1)
                )
            }

            body()

            val afterBranch = instructions.size
            val branchInst = instructions.mutableInstructions[branchIdx] as JIRIfInst
            instructions.mutableInstructions[branchIdx] = JIRIfInst(
                branchInst.location,
                branchInst.condition,
                branchInst.trueBranch,
                JIRInstRef(afterBranch)
            )
        }
    }

    private fun emitInvocation(cp: JIRClasspath, ctx: ProxyBodyContext, target: JIRMethod) {
        val receiver = ctx.parameter(0)
        val arguments = ctx.parameter(1)
        val ownerType = target.enclosingClass.toType()

        val callArgs = mutableListOf<JIRValue>()
        for ((idx, parameter) in target.parameters.withIndex()) {
            val element = ctx.local("%elem$idx", cp.objectType)
            ctx.add { loc ->
                JIRAssignInst(loc, element, JIRArrayAccess(arguments, JIRInt(idx, cp.int), cp.objectType))
            }

            val parameterType = cp.findTypeOrNull(parameter.type.typeName) ?: cp.objectType
            val casted = ctx.local("%arg$idx", parameterType)
            ctx.add { loc -> JIRAssignInst(loc, casted, JIRCastExpr(parameterType, element)) }

            callArgs += casted
        }

        val argTypeNames = target.parameters.map { it.type }
        val callExpr: JIRCallExpr = if (target.isStatic) {
            val methodRef = TypedStaticMethodRefImpl(ownerType, target.name, argTypeNames, target.returnType)
            JIRStaticCallExpr(methodRef, callArgs)
        } else {
            val castedReceiver = ctx.local("%receiver", ownerType)
            ctx.add { loc -> JIRAssignInst(loc, castedReceiver, JIRCastExpr(ownerType, receiver)) }

            JIRVirtualCallExpr(
                VirtualMethodRefImpl(ownerType, ownerType, target.name, argTypeNames, target.returnType),
                castedReceiver,
                callArgs
            )
        }

        val returnType = cp.findTypeOrNull(target.returnType.typeName)
        val result = ctx.result
        if (result == null || returnType !is JIRRefType) {
            ctx.add { loc -> JIRCallInst(loc, callExpr) }
            return
        }

        val returned = ctx.local("%returned", returnType)
        ctx.add { loc -> JIRAssignInst(loc, returned, callExpr) }
        ctx.add { loc -> JIRAssignInst(loc, result, returned) }
    }

    private fun emitFieldRead(cp: JIRClasspath, ctx: ProxyBodyContext, target: JIRField) {
        val result = ctx.result ?: return
        val fieldRef = ctx.fieldRef(cp, target, instanceParameterIndex = 0) ?: return

        val fieldType = cp.findTypeOrNull(target.type.typeName) ?: cp.objectType
        val value = ctx.local("%value", fieldType)
        ctx.add { loc -> JIRAssignInst(loc, value, fieldRef) }
        ctx.add { loc -> JIRAssignInst(loc, result, value) }
    }

    private fun emitFieldWrite(cp: JIRClasspath, ctx: ProxyBodyContext, target: JIRField) {
        val fieldRef = ctx.fieldRef(cp, target, instanceParameterIndex = 0) ?: return

        val fieldType = cp.findTypeOrNull(target.type.typeName) ?: cp.objectType
        val casted = ctx.local("%value", fieldType)
        ctx.add { loc -> JIRAssignInst(loc, casted, JIRCastExpr(fieldType, ctx.parameter(1))) }
        ctx.add { loc -> JIRAssignInst(loc, fieldRef, casted) }
    }

    private fun ProxyBodyContext.fieldRef(
        cp: JIRClasspath,
        target: JIRField,
        instanceParameterIndex: Int
    ): JIRFieldRef? {
        val ownerType = target.enclosingClass.toType()
        val typedField = JIRTypedFieldImpl(ownerType, target, JIRSubstitutorImpl.empty)

        if (target.isStatic) return JIRFieldRef(null, typedField)

        val castedInstance = local("%instance", ownerType)
        add { loc -> JIRAssignInst(loc, castedInstance, JIRCastExpr(ownerType, parameter(instanceParameterIndex))) }

        return JIRFieldRef(castedInstance, typedField)
    }

    private data class ProxyKey(val owner: String, val accessor: String, val targets: List<String>)

    companion object {
        private const val NON_DET_CLASS = "opentaint.NonDetCls"
        private const val NON_DET_METHOD = "nextBool"
        private const val BOOLEAN = "boolean"

        private val virtualLocation = VirtualLocation()

        fun JIRInstListBuilder.local(name: String, type: JIRType) = JIRLocalVar(nextLocalVarIdx(), name, type)

        fun nonDeterministicChoice(cp: JIRClasspath): JIRCallExpr {
            val nonDetClass: JIRClassType = JIRUnknownType(cp, NON_DET_CLASS, virtualLocation, nullable = false)
            val methodRef = TypedStaticMethodRefImpl(
                nonDetClass,
                NON_DET_METHOD,
                argTypes = emptyList(),
                returnType = org.opentaint.ir.impl.types.TypeNameImpl.fromTypeName(BOOLEAN)
            )
            return JIRStaticCallExpr(methodRef, emptyList())
        }
    }
}
