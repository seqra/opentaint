package org.opentaint.semgrep.pattern

// ----------------------------------------------------------------------------
// Root
// ----------------------------------------------------------------------------

sealed interface SemgrepPythonPattern {
    val children: List<SemgrepPythonPattern>

    /**
     * Fallback for grammar fragments the visitor cannot yet translate but that
     * shouldn't fail the whole parse. Real AST nodes never use this.
     */
    data class Raw(val text: String) : SemgrepPythonPattern {
        override val children: List<SemgrepPythonPattern> get() = emptyList()
    }
}

// ----------------------------------------------------------------------------
// Names
// ----------------------------------------------------------------------------

sealed interface Name
data class ConcreteName(val name: String) : Name
data class MetavarName(val name: String) : Name

// ----------------------------------------------------------------------------
// Pattern atoms / wildcards
// ----------------------------------------------------------------------------

data class Metavar(val name: String) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

data class EllipsisMetavar(val name: String) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

data object Ellipsis : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

data class DeepExpr(val nested: SemgrepPythonPattern) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOf(nested)
}

data class Identifier(val name: Name) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

// ----------------------------------------------------------------------------
// Literals
// ----------------------------------------------------------------------------

data class NumberLiteral(val text: String) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

data class BoolLiteral(val value: Boolean) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

data object NoneLiteral : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

data class StringLiteral(val content: Name) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

data object StringEllipsis : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

// ----------------------------------------------------------------------------
// Expressions
// ----------------------------------------------------------------------------

sealed interface CallArgs : SemgrepPythonPattern

data object NoArgs : CallArgs {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

data class ArgPrefix(val arg: SemgrepPythonPattern, val rest: CallArgs) : CallArgs {
    override val children: List<SemgrepPythonPattern> get() = listOf(arg, rest)
}

data class EllipsisArgPrefix(val rest: CallArgs) : CallArgs {
    override val children: List<SemgrepPythonPattern> get() = listOf(rest)
}

data class KeywordArgument(val name: Name, val value: SemgrepPythonPattern) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOf(value)
}

data class StarArgument(val value: SemgrepPythonPattern) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOf(value)
}

data class DoubleStarArgument(val value: SemgrepPythonPattern) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOf(value)
}

data class Call(
    val fn: SemgrepPythonPattern,
    val args: CallArgs,
    val hasEllipsis: Boolean,
) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOf(fn, args)
}

data class Attribute(val obj: SemgrepPythonPattern, val name: Name) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOf(obj)
}

data class Subscript(val obj: SemgrepPythonPattern, val index: SemgrepPythonPattern?) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOfNotNull(obj, index)
}

/** Any binary operator: arithmetic/bitwise (`+`), boolean (`and`/`or`), and comparison (`<`, `==`, `is not`). */
data class BinaryExpr(
    val op: String,
    val left: SemgrepPythonPattern,
    val right: SemgrepPythonPattern,
) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOf(left, right)
}

data class UnaryExpr(val op: String, val operand: SemgrepPythonPattern) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOf(operand)
}

data class TupleExpr(val elements: List<SemgrepPythonPattern>) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = elements
}

data class ListExpr(val elements: List<SemgrepPythonPattern>) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = elements
}

// ----------------------------------------------------------------------------
// Statements
// ----------------------------------------------------------------------------

data class ExprStmt(val expr: SemgrepPythonPattern) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOf(expr)
}

data object EllipsisStmt : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

/**
 * Every assignment form: plain (`a = b`), chained (`a = b = c`), augmented
 * (`a += b`, [op] is `+=`), and annotated (`a: T = b`, [annotation] set; [value]
 * null for a bare `a: T` declaration). [op] is `=` for everything but augmented.
 */
data class Assign(
    val op: String,
    val targets: List<SemgrepPythonPattern>,
    val value: SemgrepPythonPattern?,
    val annotation: SemgrepPythonPattern?,
) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = targets + listOfNotNull(annotation, value)
}

data class ReturnStmt(val value: SemgrepPythonPattern?) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOfNotNull(value)
}

data class Block(val stmts: List<SemgrepPythonPattern>) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = stmts
}

data class IfStmt(
    val cond: SemgrepPythonPattern,
    val body: Block,
    val orelse: SemgrepPythonPattern?,
) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOfNotNull(cond, body, orelse)
}

data class WhileStmt(
    val cond: SemgrepPythonPattern,
    val body: Block,
    val orelse: Block?,
) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOfNotNull(cond, body, orelse)
}

data class ForStmt(
    val target: SemgrepPythonPattern,
    val iter: SemgrepPythonPattern,
    val body: Block,
    val orelse: Block?,
) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOfNotNull(target, iter, body, orelse)
}

data class WithStmt(
    val items: List<WithItem>,
    val body: Block,
) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = items + body
}

data class WithItem(val context: SemgrepPythonPattern, val asTarget: SemgrepPythonPattern?) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOfNotNull(context, asTarget)
}

data object PassStmt : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

data object BreakStmt : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

data object ContinueStmt : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

// ----------------------------------------------------------------------------
// Imports
// ----------------------------------------------------------------------------

data class ImportAlias(val dottedName: List<Name>, val asName: Name?)

data class ImportStmt(val names: List<ImportAlias>) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

data class FromImportStmt(
    val module: List<Name>,
    val names: List<ImportAlias>,
    val importStar: Boolean,
) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

// ----------------------------------------------------------------------------
// Declarations
// ----------------------------------------------------------------------------

sealed interface Param : SemgrepPythonPattern

data class NamedParam(
    val name: Name,
    val annotation: SemgrepPythonPattern?,
    val default: SemgrepPythonPattern?,
) : Param {
    override val children: List<SemgrepPythonPattern> get() = listOfNotNull(annotation, default)
}

data object EllipsisParam : Param {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

data class StarParam(val name: Name?) : Param {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

data class DoubleStarParam(val name: Name?) : Param {
    override val children: List<SemgrepPythonPattern> get() = emptyList()
}

data class FunctionDef(
    val name: Name,
    val params: List<Param>,
    val body: Block,
    val decorators: List<SemgrepPythonPattern>,
    val returns: SemgrepPythonPattern?,
    val isAsync: Boolean,
) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern>
        get() = params + decorators + listOfNotNull(returns) + body
}

data class ClassDef(
    val name: Name,
    val bases: CallArgs,
    val body: Block,
    val decorators: List<SemgrepPythonPattern>,
) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = listOf(bases) + decorators + body
}

// ----------------------------------------------------------------------------
// Top level
// ----------------------------------------------------------------------------

data class TopList(val items: List<SemgrepPythonPattern>) : SemgrepPythonPattern {
    override val children: List<SemgrepPythonPattern> get() = items
}
