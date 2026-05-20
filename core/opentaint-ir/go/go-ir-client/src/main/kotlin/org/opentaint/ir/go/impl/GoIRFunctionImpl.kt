package org.opentaint.ir.go.impl

import org.opentaint.ir.go.api.*
import org.opentaint.ir.go.type.GoIRFuncType

class GoIRFunctionImpl(
    override val name: String,
    override val fullName: String,
    override val pkg: GoIRPackage?,
    override val signature: GoIRFuncType,
    override val params: List<GoIRParameter>,
    override val freeVars: List<GoIRFreeVar>,
    override val position: GoIRPosition?,
    override val isMethod: Boolean,
    override val isPointerReceiver: Boolean,
    override val isExported: Boolean,
    override val isSynthetic: Boolean,
    override val syntheticKind: String?,
    private val declaredHasBody: Boolean = false,
    private val bodyLoader: (() -> Unit)? = null,
    // Deferred resolution fields
    internal val receiverTypeId: Int = 0,
    internal val parentFunctionId: Int = 0,
    internal val anonFunctionIds: List<Int> = emptyList(),
) : GoIRFunction {
    private val bodyLock = Any()
    @Volatile private var bodyLoadAttempted = bodyLoader == null
    private var _body: GoIRBody? = null

    override val body: GoIRBody?
        get() {
            if (_body == null && declaredHasBody && !bodyLoadAttempted) {
                synchronized(bodyLock) {
                    if (_body == null && !bodyLoadAttempted) {
                        bodyLoader?.invoke()
                        bodyLoadAttempted = true
                    }
                }
            }
            return _body
        }

    override val hasBody: Boolean get() = declaredHasBody

    override var receiverType: GoIRNamedType? = null
        internal set

    override var parent: GoIRFunction? = null
        internal set

    private val _anonymousFunctions = mutableListOf<GoIRFunction>()
    override val anonymousFunctions: List<GoIRFunction> get() = _anonymousFunctions

    override val typeParams: List<GoIRTypeParamDecl> = emptyList() // TODO: implement

    fun setBody(body: GoIRBody) {
        this._body = body
        this.bodyLoadAttempted = true
    }

    fun resolveReferences(
        functionsById: Map<Int, GoIRFunctionImpl>,
        namedTypesById: Map<Int, GoIRNamedTypeImpl>,
    ) {
        if (parentFunctionId != 0) {
            parent = functionsById[parentFunctionId]
        }
        for (id in anonFunctionIds) {
            functionsById[id]?.let { _anonymousFunctions.add(it) }
        }
        // receiverType is resolved externally via resolveReceiverType after type
        // references have been linked, because receiverTypeId is a type ID (not a
        // named-type ID) and methods may not be referenced from any named type's
        // method list (e.g. pointer-wrapper synthetic methods).
    }

    fun resolveReceiverType(named: GoIRNamedType) {
        if (receiverType == null) {
            receiverType = named
        }
    }

    override fun toString(): String = "GoIRFunction($fullName)"
}
