package org.opentaint.dataflow.python.graph

import org.opentaint.ir.api.python.PIRAnyType
import org.opentaint.ir.api.python.PIRCFG
import org.opentaint.ir.api.python.PIRCallArgKind
import org.opentaint.ir.api.python.PIRClass
import org.opentaint.ir.api.python.PIRDecorator
import org.opentaint.ir.api.python.PIRDiagnostic
import org.opentaint.ir.api.python.PIRField
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.ir.api.python.PIRModule
import org.opentaint.ir.api.python.PIRParameter
import org.opentaint.ir.api.python.PIRType
import org.opentaint.ir.impl.python.PIRCFGImpl

data class StrippedCallArg(val kind: PIRCallArgKind, val keyword: String?)

/**
 * Synthetic [PIRFunction]s produced by [org.opentaint.dataflow.python.PIRCallResolver] when a call's callee
 * cannot be resolved to a real function in the classpath. Two precision levels:
 *
 * - [PIRQualifiedUnknownFunction]: a fully-qualified name was reconstructed
 *   (e.g. `os.path.join`) but no body is loaded — taint rules keyed on the FQN
 *   can match.
 * - [PIRSimpleNameUnknownFunction]: only the trailing attribute segment is
 *   known (e.g. `encode` from `obj.encode(...)`) — taint rules keyed on the
 *   simple name can match.
 *
 * Both are filtered out of interprocedural stepping by
 * [org.opentaint.dataflow.python.analysis.PIRMethodCallResolver.realCallees] via the common [PIRUnknownFunction]
 * supertype.
 */
sealed interface PIRUnknownFunction : PIRFunction {
    val callArgs: List<StrippedCallArg>
    val hasVarPositionalArg: Boolean get() = callArgs.any { it.kind == PIRCallArgKind.STAR }
    val positionalArgIndices: List<Int> get() = callArgs.indices.filter { callArgs[it].kind == PIRCallArgKind.POSITIONAL }

    override val parameters: List<PIRParameter> get() = emptyList()
    override val returnType: PIRType get() = PIRAnyType
    override val cfg: PIRCFG get() = PIRCFGImpl.EMPTY_CFG
    override val instList: List<PIRInstruction> get() = emptyList()
    override val decorators: List<PIRDecorator> get() = emptyList()
    override val isAsync: Boolean get() = false
    override val isGenerator: Boolean get() = false
    override val isStaticMethod: Boolean get() = false
    override val isClassMethod: Boolean get() = false
    override val isProperty: Boolean get() = false
    override val closureVars: List<String> get() = emptyList()
    override val enclosingClass: PIRClass? get() = null
}

data class PIRQualifiedUnknownFunction(
    override val qualifiedName: String,
    override val callArgs: List<StrippedCallArg>,
) : PIRUnknownFunction {
    override val name: String get() = qualifiedName.substringAfterLast('.')
    override val module: PIRModule = SimpleNameSyntheticModule(qualifiedName.substringBeforeLast('.'))
}

data class PIRSimpleNameUnknownFunction(
    override val name: String,
    override val callArgs: List<StrippedCallArg>,
) : PIRUnknownFunction {
    override val qualifiedName: String get() = name
    override val module: PIRModule = SimpleNameSyntheticModule("")
}

private class SimpleNameSyntheticModule(override val name: String) : PIRModule {
    override val path: String = ""
    override val classes: List<PIRClass> = emptyList()
    override val functions: List<PIRFunction> = emptyList()
    override val fields: List<PIRField> = emptyList()
    override val imports: List<String> = emptyList()
    override val diagnostics: List<PIRDiagnostic> = emptyList()
    override val isUnknown: Boolean = true
    override val moduleInit: PIRFunction
        get() = error("Synthetic simple-name module has no init")
}
