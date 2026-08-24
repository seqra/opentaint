package org.opentaint.ir.impl.python.flat

import org.opentaint.ir.api.python.PIRDiagnostic

enum class FlatFunctionKind {
    MODULE_INIT,
    TOP_LEVEL,
    METHOD,
    NESTED_DEF,
    LAMBDA,
}

data class FlatFunctionIR(
    val name: String,
    val qualifiedName: String,
    val parentQualifiedName: String?,
    val kind: FlatFunctionKind,
    val cfg: FlatCFG,
    val parameters: List<FlatParameter>,
    val returnType: FlatType,
    val isAsync: Boolean,
    val isGenerator: Boolean,
    val decorators: List<FlatDecorator>,
    val closureVars: Set<String> = emptySet(),
    val nonlocalNames: Set<String> = emptySet(),
    val globalNames: Set<String> = emptySet(),
) {
    val isStaticMethod: Boolean get() = decorators.any { it.name == "staticmethod" }
    val isClassMethod: Boolean get() = decorators.any { it.name == "classmethod" }
    val isProperty: Boolean get() = decorators.any { it.name == "property" }
}

data class FlatParameter(
    val name: String,
    val type: FlatType,
    val kind: FlatParamKind,
    val hasDefault: Boolean,
    val defaultValue: FlatConst?,
)

enum class FlatParamKind {
    POSITIONAL_OR_KEYWORD,
    VAR_POSITIONAL,
    VAR_KEYWORD,
    KEYWORD_ONLY,
}

data class FlatDecorator(
    val name: String,
    val qualifiedName: String,
    val arguments: List<String>,
)

data class FlatModuleField(
    val name: String,
    val type: FlatType,
    val hasInitializer: Boolean,
)

data class FlatClassField(
    val name: String,
    val type: FlatType,
    val isClassVar: Boolean,
)

data class FlatClass(
    val name: String,
    val qualifiedName: String,
    val baseClasses: List<String>,
    val mro: List<String>,
    val methods: List<FlatFunctionIR>,
    val fields: List<FlatClassField>,
    val nestedClasses: List<FlatClass>,
    val decorators: List<FlatDecorator>,
    val isAbstract: Boolean,
    val isDataclass: Boolean,
    val isEnum: Boolean,
)

data class FlatModuleIR(
    val moduleName: String,
    val path: String,
    val functions: List<FlatFunctionIR>,
    val moduleInit: FlatFunctionIR,
    val classes: List<FlatClass>,
    val fields: List<FlatModuleField>,
    val imports: List<String>,
    val diagnostics: List<PIRDiagnostic>,
) {
    init {
        require(moduleInit.kind == FlatFunctionKind.MODULE_INIT) {
            "moduleInit must have kind=MODULE_INIT, got ${moduleInit.kind}"
        }
        require(functions.none { it.kind == FlatFunctionKind.MODULE_INIT }) {
            "functions must not contain a MODULE_INIT entry"
        }
    }
}
