package org.opentaint.dataflow.jvm.ap.ifds.reflection

import org.objectweb.asm.Opcodes
import org.opentaint.ir.api.jvm.JIRClassOrInterface
import org.opentaint.ir.api.jvm.JIRClasspath
import org.opentaint.ir.api.jvm.JIRDeclaration
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.RegisteredLocation
import org.opentaint.ir.api.jvm.TypeName
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRInstList
import org.opentaint.ir.impl.bytecode.JIRDeclarationImpl
import org.opentaint.ir.impl.features.classpaths.VirtualLocation
import org.opentaint.ir.impl.features.classpaths.virtual.JIRVirtualClassImpl
import org.opentaint.ir.impl.features.classpaths.virtual.JIRVirtualField
import org.opentaint.ir.impl.features.classpaths.virtual.JIRVirtualMethod
import org.opentaint.ir.impl.features.classpaths.virtual.JIRVirtualMethodImpl
import org.opentaint.ir.impl.features.classpaths.virtual.JIRVirtualParameter
import java.util.Objects
import java.util.concurrent.CopyOnWriteArrayList

class JIRReflectionProxyClass(
    name: String,
    private val proxyMethods: CopyOnWriteArrayList<JIRVirtualMethod> = CopyOnWriteArrayList()
) : JIRVirtualClassImpl(name, initialFields = emptyList(), initialMethods = proxyMethods) {

    private lateinit var declarationLocation: RegisteredLocation

    override val isAnonymous: Boolean get() = false

    override val interfaces: List<JIRClassOrInterface> get() = emptyList()

    override val declaredFields: List<JIRVirtualField> get() = emptyList()

    override val declaration: JIRDeclaration
        get() = JIRDeclarationImpl.of(declarationLocation, this)

    override fun bind(classpath: JIRClasspath, virtualLocation: VirtualLocation) {
        bindWithLocation(classpath, virtualLocation)
    }

    fun bindWithLocation(classpath: JIRClasspath, location: RegisteredLocation) {
        this.classpath = classpath
        this.declarationLocation = location
    }

    fun addProxyMethod(method: JIRVirtualMethod) {
        proxyMethods += method
    }

    override fun hashCode(): Int = name.hashCode()

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        return other is JIRReflectionProxyClass && name == other.name
    }

    override fun toString(): String = "(reflection proxy: $name)"
}

class JIRReflectionProxyMethod(
    name: String,
    returnType: TypeName,
    description: String,
    parameters: List<JIRVirtualParameter>,
    val targets: List<JIRMethod>,
    private val instructions: JIRInstList<JIRInst>
) : JIRVirtualMethodImpl(
    name,
    access = Opcodes.ACC_PUBLIC or Opcodes.ACC_STATIC,
    returnType = returnType,
    parameters = parameters,
    description = description
) {
    override val instList: JIRInstList<JIRInst> get() = instructions

    override fun hashCode(): Int = Objects.hash(name, enclosingClass)

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        return other is JIRReflectionProxyMethod && name == other.name && enclosingClass == other.enclosingClass
    }
}
