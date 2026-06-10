package org.opentaint.semgrep.pattern

import org.antlr.v4.runtime.BaseErrorListener
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.ConsoleErrorListener
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.RecognitionException
import org.antlr.v4.runtime.Recognizer
import org.antlr.v4.runtime.tree.TerminalNode
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternParser
import org.opentaint.semgrep.pattern.python.antlr.PythonLexer
import org.opentaint.semgrep.pattern.python.antlr.PythonParser
import org.opentaint.semgrep.pattern.python.antlr.PythonParserBaseVisitor

sealed interface SemgrepPythonPatternParsingResult {
    data class Ok(val pattern: SemgrepPythonPattern) : SemgrepPythonPatternParsingResult
    data class ParserFailure(val exception: SemgrepPythonParsingException) : SemgrepPythonPatternParsingResult
    data class OtherFailure(val exception: Throwable) : SemgrepPythonPatternParsingResult
    data class FailedASTParsing(val errorMessages: List<String>) : SemgrepPythonPatternParsingResult
}

sealed class SemgrepPythonParsingException(val element: ParserRuleContext, message: String) : Exception(message)

class SemgrepPythonParsingFailedException(ctx: ParserRuleContext, additionalMessage: String) :
    SemgrepPythonParsingException(ctx, "Exception during parsing ${ctx.text}: $additionalMessage")

class UnsupportedPythonElement(element: ParserRuleContext) :
    SemgrepPythonParsingException(element, "Unsupported element: ${element.text}")

class SemgrepPythonPatternParser : SemgrepPatternParser<SemgrepPythonPattern> {
    private val visitor = SemgrepPythonPatternParserVisitor()

    override fun parseOrNull(pattern: String, semgrepTrace: SemgrepRuleLoadStepTrace): SemgrepPythonPattern? =
        when (val r = parseSemgrepPythonPattern(pattern)) {
            is SemgrepPythonPatternParsingResult.Ok -> r.pattern
            is SemgrepPythonPatternParsingResult.FailedASTParsing -> {
                semgrepTrace.error(PatternParsingAstFailed(r.errorMessages))
                null
            }
            is SemgrepPythonPatternParsingResult.ParserFailure -> {
                semgrepTrace.error(PatternParsingFailure(r.exception.message))
                null
            }
            is SemgrepPythonPatternParsingResult.OtherFailure -> {
                semgrepTrace.error(PatternParsingFailure(r.exception.message))
                null
            }
        }

    fun parseSemgrepPythonPattern(pattern: String): SemgrepPythonPatternParsingResult {
        val errors = mutableListOf<String>()

        val lexer = PythonLexer(CharStreams.fromString(pattern)).apply { configureErrorListener(errors) }
        val tokens = CommonTokenStream(lexer)
        val parser = PythonParser(tokens).apply { configureErrorListener(errors) }

        val tree = try {
            parser.semgrepPattern()
        } catch (t: Throwable) {
            return SemgrepPythonPatternParsingResult.OtherFailure(t)
        }
        if (errors.isNotEmpty()) {
            return SemgrepPythonPatternParsingResult.FailedASTParsing(errors)
        }

        return try {
            val ast = visitor.visit(tree)
                ?: return SemgrepPythonPatternParsingResult.OtherFailure(IllegalStateException("Null AST"))
            SemgrepPythonPatternParsingResult.Ok(ast)
        } catch (e: SemgrepPythonParsingException) {
            SemgrepPythonPatternParsingResult.ParserFailure(e)
        } catch (t: Throwable) {
            SemgrepPythonPatternParsingResult.OtherFailure(t)
        }
    }

    private fun Recognizer<*, *>.configureErrorListener(errors: MutableList<String>) {
        removeErrorListener(ConsoleErrorListener.INSTANCE)
        addErrorListener(object : BaseErrorListener() {
            override fun syntaxError(
                recognizer: Recognizer<*, *>?,
                offendingSymbol: Any?,
                line: Int,
                charPositionInLine: Int,
                msg: String,
                e: RecognitionException?
            ) {
                errors.add("line $line:$charPositionInLine $msg")
            }
        })
    }
}

// ----------------------------------------------------------------------------
// Visitor
// ----------------------------------------------------------------------------

private class SemgrepPythonPatternParserVisitor : PythonParserBaseVisitor<SemgrepPythonPattern?>() {

    // --- top level ---

    override fun visitSemgrepPattern(ctx: PythonParser.SemgrepPatternContext): SemgrepPythonPattern {
        ctx.eval_input()?.let { return parseEvalInput(it) }
        ctx.file_input()?.let {
            val stmts = parseFileInput(it)
            return stmts.singleOrNull() ?: TopList(stmts)
        }
        throw UnsupportedPythonElement(ctx)
    }

    private fun parseEvalInput(ctx: PythonParser.Eval_inputContext): SemgrepPythonPattern =
        parseTestlist(ctx.testlist())

    private fun parseFileInput(ctx: PythonParser.File_inputContext): List<SemgrepPythonPattern> =
        ctx.stmt().flatMap { parseStmt(it) }

    // --- statements ---

    private fun parseStmt(ctx: PythonParser.StmtContext): List<SemgrepPythonPattern> {
        ctx.simple_stmt()?.let { s -> return s.small_stmt().map { parseSmallStmt(it) } }
        ctx.compound_stmt()?.let { return listOf(parseCompoundStmt(it)) }
        throw UnsupportedPythonElement(ctx)
    }

    private fun parseSmallStmt(ctx: PythonParser.Small_stmtContext): SemgrepPythonPattern =
        when (ctx) {
            is PythonParser.Expr_stmtContext -> parseExprStmt(ctx)
            is PythonParser.Return_stmtContext -> ReturnStmt(ctx.testlist()?.let { parseTestlist(it) })
            is PythonParser.Pass_stmtContext -> PassStmt
            is PythonParser.Break_stmtContext -> BreakStmt
            is PythonParser.Continue_stmtContext -> ContinueStmt
            is PythonParser.Import_stmtContext -> parseImport(ctx)
            is PythonParser.From_stmtContext -> parseFromImport(ctx)
            else -> SemgrepPythonPattern.Raw(ctx.text)
        }

    private fun parseExprStmt(ctx: PythonParser.Expr_stmtContext): SemgrepPythonPattern {
        val lhs = parseTestlistStarExpr(ctx.testlist_star_expr())
        val ap = ctx.assign_part()
            ?: return if (lhs is Ellipsis) EllipsisStmt else ExprStmt(lhs)

        // Plain / chained assignment: `a = b = c`
        if (ap.ASSIGN().isNotEmpty() && ap.testlist_star_expr().isNotEmpty()) {
            val rhs = ap.testlist_star_expr().map { parseTestlistStarExpr(it) }
            val value = rhs.last()
            val targets = listOf(lhs) + rhs.dropLast(1)
            return Assign("=", targets, value, annotation = null)
        }
        // Annotated assignment: `a : T (= v)?`
        ap.COLON()?.let {
            val annotation = parseTest(ap.test())
            val value = ap.testlist()?.let { tl -> parseTestlist(tl) }
            return Assign("=", listOf(lhs), value, annotation)
        }
        // Augmented assignment: `a += b`
        val opToken = (0 until ap.childCount)
            .map { ap.getChild(it) }
            .filterIsInstance<TerminalNode>()
            .firstOrNull()
        val value = ap.testlist()?.let { parseTestlist(it) }
        if (opToken != null && value != null) {
            return Assign(opToken.text, listOf(lhs), value, annotation = null)
        }
        return SemgrepPythonPattern.Raw(ctx.text)
    }

    private fun parseImport(ctx: PythonParser.Import_stmtContext): SemgrepPythonPattern {
        val aliases = ctx.dotted_as_names().dotted_as_name().map { dan ->
            ImportAlias(parseDottedName(dan.dotted_name()), dan.name()?.let { parseName(it) })
        }
        return ImportStmt(aliases)
    }

    private fun parseFromImport(ctx: PythonParser.From_stmtContext): SemgrepPythonPattern {
        val module = ctx.dotted_name()?.let { parseDottedName(it) }.orEmpty()
        val star = ctx.STAR() != null
        val aliases = ctx.import_as_names()?.import_as_name()?.map { ian ->
            val names = ian.name()
            ImportAlias(listOf(parseName(names[0])), names.getOrNull(1)?.let { parseName(it) })
        }.orEmpty()
        return FromImportStmt(module, aliases, star)
    }

    private fun parseCompoundStmt(ctx: PythonParser.Compound_stmtContext): SemgrepPythonPattern =
        when (ctx) {
            is PythonParser.If_stmtContext -> parseIf(ctx)
            is PythonParser.While_stmtContext -> parseWhile(ctx)
            is PythonParser.For_stmtContext -> parseFor(ctx)
            is PythonParser.With_stmtContext -> parseWith(ctx)
            is PythonParser.Class_or_func_def_stmtContext -> parseClassOrFunc(ctx)
            else -> SemgrepPythonPattern.Raw(ctx.text)
        }

    private fun parseIf(ctx: PythonParser.If_stmtContext): SemgrepPythonPattern {
        val cond = parseTest(ctx.test())
        val body = parseSuite(ctx.suite())
        // Build elif chain from the tail; attach final else if present.
        var orelse: SemgrepPythonPattern? = ctx.else_clause()?.let { parseSuite(it.suite()) }
        for (elif in ctx.elif_clause().reversed()) {
            orelse = IfStmt(parseTest(elif.test()), parseSuite(elif.suite()), orelse)
        }
        return IfStmt(cond, body, orelse)
    }

    private fun parseWhile(ctx: PythonParser.While_stmtContext): SemgrepPythonPattern {
        val orelse = ctx.else_clause()?.let { parseSuite(it.suite()) }
        return WhileStmt(parseTest(ctx.test()), parseSuite(ctx.suite()), orelse)
    }

    private fun parseFor(ctx: PythonParser.For_stmtContext): SemgrepPythonPattern {
        val target = parseExprlist(ctx.exprlist())
        val iter = parseTestlist(ctx.testlist())
        val orelse = ctx.else_clause()?.let { parseSuite(it.suite()) }
        return ForStmt(target, iter, parseSuite(ctx.suite()), orelse)
    }

    private fun parseWith(ctx: PythonParser.With_stmtContext): SemgrepPythonPattern {
        val items = ctx.with_item().map { wi ->
            WithItem(parseTest(wi.test()), wi.expr()?.let { parseExpr(it) })
        }
        return WithStmt(items, parseSuite(ctx.suite()))
    }

    private fun parseClassOrFunc(ctx: PythonParser.Class_or_func_def_stmtContext): SemgrepPythonPattern {
        val decorators = ctx.decorator().map { parseDecorator(it) }
        ctx.funcdef()?.let { return parseFuncdef(it, decorators) }
        ctx.classdef()?.let { return parseClassdef(it, decorators) }
        throw UnsupportedPythonElement(ctx)
    }

    private fun parseDecorator(ctx: PythonParser.DecoratorContext): SemgrepPythonPattern {
        val name = parseDottedNameExpr(ctx.dotted_name())
        return if (ctx.OPEN_PAREN() != null) {
            val args = parseArglist(ctx.arglist())
            Call(name, args, hasEllipsis = args.containsEllipsis())
        } else {
            name
        }
    }

    private fun parseFuncdef(
        ctx: PythonParser.FuncdefContext,
        decorators: List<SemgrepPythonPattern>,
    ): SemgrepPythonPattern {
        val name = parseName(ctx.name())
        val params = ctx.typedargslist()?.let { parseParams(it) }.orEmpty()
        val returns = ctx.test()?.let { parseTest(it) }
        return FunctionDef(name, params, parseSuite(ctx.suite()), decorators, returns, isAsync = ctx.ASYNC() != null)
    }

    private fun parseClassdef(
        ctx: PythonParser.ClassdefContext,
        decorators: List<SemgrepPythonPattern>,
    ): SemgrepPythonPattern {
        val name = parseName(ctx.name())
        val bases = if (ctx.OPEN_PAREN() != null) parseArglist(ctx.arglist()) else NoArgs
        return ClassDef(name, bases, parseSuite(ctx.suite()), decorators)
    }

    private fun parseParams(ctx: PythonParser.TypedargslistContext): List<Param> {
        val params = mutableListOf<Param>()
        // Walk children in order so ellipsis position is preserved.
        for (i in 0 until ctx.childCount) {
            when (val c = ctx.getChild(i)) {
                is PythonParser.Def_parametersContext -> c.def_parameter().forEach { params.add(parseDefParameter(it)) }
                is PythonParser.ArgsContext -> params.add(StarParam(c.named_parameter()?.name()?.let { parseName(it) }))
                is PythonParser.KwargsContext -> params.add(DoubleStarParam(c.named_parameter()?.name()?.let { parseName(it) }))
            }
        }
        return params
    }

    private fun parseDefParameter(ctx: PythonParser.Def_parameterContext): Param {
        if (ctx.ELLIPSIS() != null) return EllipsisParam
        ctx.named_parameter()?.let { np ->
            val name = parseName(np.name())
            val annotation = np.test()?.let { parseTest(it) }
            val default = ctx.test()?.let { parseTest(it) }
            return NamedParam(name, annotation, default)
        }
        // bare `*`
        return StarParam(null)
    }

    private fun parseSuite(ctx: PythonParser.SuiteContext): Block {
        ctx.simple_stmt()?.let { s -> return Block(s.small_stmt().map { parseSmallStmt(it) }) }
        return Block(ctx.stmt().flatMap { parseStmt(it) })
    }

    // --- expressions ---

    private fun parseTestlist(ctx: PythonParser.TestlistContext): SemgrepPythonPattern {
        val tests = ctx.test().map { parseTest(it) }
        return tests.singleOrNull() ?: TupleExpr(tests)
    }

    private fun parseTestlistStarExpr(ctx: PythonParser.Testlist_star_exprContext): SemgrepPythonPattern {
        ctx.testlist()?.let { return parseTestlist(it) }
        val elements = collectInOrder(ctx)
        return elements.singleOrNull() ?: TupleExpr(elements)
    }

    private fun collectInOrder(ctx: PythonParser.Testlist_star_exprContext): List<SemgrepPythonPattern> {
        val out = mutableListOf<SemgrepPythonPattern>()
        for (i in 0 until ctx.childCount) {
            when (val c = ctx.getChild(i)) {
                is PythonParser.TestContext -> out.add(parseTest(c))
                is PythonParser.Star_exprContext -> out.add(StarArgument(parseExpr(c.expr())))
            }
        }
        return out
    }

    private fun parseExprlist(ctx: PythonParser.ExprlistContext): SemgrepPythonPattern {
        val exprs = ctx.expr().map { parseExpr(it) }
        return exprs.singleOrNull() ?: TupleExpr(exprs)
    }

    private fun parseTest(ctx: PythonParser.TestContext): SemgrepPythonPattern {
        // Ternary (`a if c else b`) and lambda are outside the supported subset.
        if (ctx.IF() != null || ctx.LAMBDA() != null) return SemgrepPythonPattern.Raw(ctx.text)
        return parseLogicalTest(ctx.logical_test(0))
    }

    private fun parseLogicalTest(ctx: PythonParser.Logical_testContext): SemgrepPythonPattern {
        ctx.comparison()?.let { return parseComparison(it) }
        val sub = ctx.logical_test()
        if (ctx.NOT() != null && sub.size == 1) return UnaryExpr("not", parseLogicalTest(sub[0]))
        if (sub.size == 2) {
            val op = if (ctx.AND() != null) "and" else "or"
            return BinaryExpr(op, parseLogicalTest(sub[0]), parseLogicalTest(sub[1]))
        }
        throw UnsupportedPythonElement(ctx)
    }

    private fun parseComparison(ctx: PythonParser.ComparisonContext): SemgrepPythonPattern {
        ctx.expr()?.let { if (ctx.comparison().isEmpty()) return parseExpr(it) }
        val sub = ctx.comparison()
        if (sub.size == 2) {
            val op = (0 until ctx.childCount)
                .map { ctx.getChild(it) }
                .filterIsInstance<TerminalNode>()
                .joinToString(" ") { it.text }
            return BinaryExpr(op, parseComparison(sub[0]), parseComparison(sub[1]))
        }
        throw UnsupportedPythonElement(ctx)
    }

    private fun parseExpr(ctx: PythonParser.ExprContext): SemgrepPythonPattern {
        ctx.atom()?.let { atom ->
            var base = parseAtom(atom)
            for (tr in ctx.trailer()) {
                base = parseTrailer(base, tr)
            }
            return base
        }
        val sub = ctx.expr()
        if (sub.size == 1) {
            val op = ctx.getChild(0) as? TerminalNode
            return UnaryExpr(op?.text ?: "?", parseExpr(sub[0]))
        }
        if (sub.size == 2) {
            val op = (1 until ctx.childCount)
                .firstNotNullOfOrNull { ctx.getChild(it) as? TerminalNode }
                ?.text ?: "?"
            return BinaryExpr(op, parseExpr(sub[0]), parseExpr(sub[1]))
        }
        throw UnsupportedPythonElement(ctx)
    }

    private fun parseTrailer(base: SemgrepPythonPattern, tr: PythonParser.TrailerContext): SemgrepPythonPattern {
        if (tr.DOT() != null) {
            val attr = Attribute(base, parseName(tr.name()))
            return tr.arguments()?.let { buildCallOrSubscript(attr, it) } ?: attr
        }
        tr.arguments()?.let { return buildCallOrSubscript(base, it) }
        return base
    }

    private fun buildCallOrSubscript(
        base: SemgrepPythonPattern,
        ctx: PythonParser.ArgumentsContext,
    ): SemgrepPythonPattern {
        if (ctx.OPEN_PAREN() != null) {
            val args = parseArglist(ctx.arglist())
            return Call(base, args, hasEllipsis = args.containsEllipsis())
        }
        val index = ctx.subscriptlist()?.let { parseSubscriptlist(it) }
        return Subscript(base, index)
    }

    private fun parseSubscriptlist(ctx: PythonParser.SubscriptlistContext): SemgrepPythonPattern {
        val subs = ctx.subscript().map { parseSubscript(it) }
        return subs.singleOrNull() ?: TupleExpr(subs)
    }

    private fun parseSubscript(ctx: PythonParser.SubscriptContext): SemgrepPythonPattern {
        if (ctx.ELLIPSIS() != null) return Ellipsis
        val tests = ctx.test()
        // Plain index `a[i]`; slices fall back to Raw for now.
        if (ctx.COLON() == null && tests.size == 1) return parseTest(tests[0])
        return SemgrepPythonPattern.Raw(ctx.text)
    }

    private fun parseArglist(ctx: PythonParser.ArglistContext?): CallArgs {
        if (ctx == null) return NoArgs
        return ctx.argument().foldRight<PythonParser.ArgumentContext, CallArgs>(NoArgs) { argCtx, rest ->
            when (val arg = parseArgument(argCtx)) {
                is Ellipsis -> if (rest is EllipsisArgPrefix) rest else EllipsisArgPrefix(rest)
                else -> ArgPrefix(arg, rest)
            }
        }
    }

    private fun parseArgument(ctx: PythonParser.ArgumentContext): SemgrepPythonPattern {
        val tests = ctx.test()
        if (ctx.POWER() != null) return DoubleStarArgument(parseTest(tests[0]))
        if (ctx.STAR() != null) return StarArgument(parseTest(tests[0]))
        if (ctx.comp_for() != null) return SemgrepPythonPattern.Raw(ctx.text)
        if (ctx.ASSIGN() != null && tests.size == 2) {
            return KeywordArgument(exprToName(parseTest(tests[0]), ctx), parseTest(tests[1]))
        }
        return parseTest(tests[0])
    }

    private fun exprToName(p: SemgrepPythonPattern, ctx: ParserRuleContext): Name =
        when (p) {
            is Identifier -> p.name
            is Metavar -> MetavarName(p.name)
            else -> ConcreteName(ctx.text.substringBefore('=').trim())
        }

    // --- atoms ---

    private fun parseAtom(ctx: PythonParser.AtomContext): SemgrepPythonPattern {
        ctx.ELLIPSIS()?.let { return Ellipsis }
        ctx.LDOTS()?.let { return DeepExpr(parseTest(ctx.test())) }
        ctx.name()?.let { return atomFromName(parseName(it)) }
        ctx.NONE()?.let { return NoneLiteral }
        ctx.number()?.let {
            val text = if (ctx.MINUS() != null) "-${it.text}" else it.text
            return NumberLiteral(text)
        }
        if (ctx.STRING().isNotEmpty()) return parseStringAtom(ctx.STRING().map { it.text })
        ctx.PRINT()?.let { return Identifier(ConcreteName("print")) }
        ctx.EXEC()?.let { return Identifier(ConcreteName("exec")) }
        // ( ... ) tuple / parenthesized, [ ... ] list
        if (ctx.OPEN_PAREN() != null) {
            val tc = ctx.testlist_comp() ?: return SemgrepPythonPattern.Raw(ctx.text)
            val elems = parseTestlistComp(tc)
            return if (elems.size == 1 && tc.COMMA().isEmpty()) elems[0] else TupleExpr(elems)
        }
        if (ctx.OPEN_BRACKET() != null) {
            val elems = ctx.testlist_comp()?.let { parseTestlistComp(it) }.orEmpty()
            return ListExpr(elems)
        }
        return SemgrepPythonPattern.Raw(ctx.text)
    }

    private fun parseTestlistComp(ctx: PythonParser.Testlist_compContext): List<SemgrepPythonPattern> {
        if (ctx.comp_for() != null) return listOf(SemgrepPythonPattern.Raw(ctx.text))
        val out = mutableListOf<SemgrepPythonPattern>()
        for (i in 0 until ctx.childCount) {
            when (val c = ctx.getChild(i)) {
                is PythonParser.TestContext -> out.add(parseTest(c))
                is PythonParser.Star_exprContext -> out.add(StarArgument(parseExpr(c.expr())))
            }
        }
        return out
    }

    private fun atomFromName(name: Name): SemgrepPythonPattern =
        when (name) {
            is MetavarName -> if (name.name.startsWith("...")) EllipsisMetavar(name.name.removePrefix("...")) else Metavar(name.name)
            is ConcreteName -> Identifier(name)
        }

    private fun parseStringAtom(parts: List<String>): SemgrepPythonPattern {
        if (parts.size == 1) {
            val inner = unquoteString(parts[0])
            if (inner == "...") return StringEllipsis
            if (isMetavarText(inner)) return StringLiteral(MetavarName(inner))
            return StringLiteral(ConcreteName(inner))
        }
        return StringLiteral(ConcreteName(parts.joinToString("") { unquoteString(it) }))
    }

    // --- names ---

    private fun parseName(ctx: PythonParser.NameContext): Name {
        ctx.METAVAR()?.let { return MetavarName(it.text) }
        ctx.METAVAR_ELLIPSIS()?.let { return MetavarName(it.text.removePrefix("$")) } // "$...X" -> "...X"
        ctx.ANONYMOUS_METAVAR()?.let { return MetavarName("_") }
        return ConcreteName(ctx.text)
    }

    private fun parseDottedName(ctx: PythonParser.Dotted_nameContext): List<Name> {
        val parts = mutableListOf<Name>()
        fun walk(c: PythonParser.Dotted_nameContext) {
            c.dotted_name()?.let { walk(it) }
            parts.add(parseName(c.name()))
        }
        walk(ctx)
        return parts
    }

    private fun parseDottedNameExpr(ctx: PythonParser.Dotted_nameContext): SemgrepPythonPattern {
        val names = parseDottedName(ctx)
        var base: SemgrepPythonPattern = atomFromName(names.first())
        for (n in names.drop(1)) base = Attribute(base, n)
        return base
    }
}

// ----------------------------------------------------------------------------
// Helpers
// ----------------------------------------------------------------------------

private tailrec fun CallArgs.containsEllipsis(): Boolean =
    when (this) {
        is NoArgs -> false
        is EllipsisArgPrefix -> true
        is ArgPrefix -> rest.containsEllipsis()
    }

private fun isMetavarText(s: String): Boolean =
    s.length >= 2 && s[0] == '$' && (s[1].isUpperCase() || s[1] == '_') &&
        s.drop(1).all { it.isUpperCase() || it.isDigit() || it == '_' }

private fun unquoteString(raw: String): String {
    var s = raw
    // strip string prefixes (r, b, f, u and combinations)
    val quoteIdx = s.indexOfFirst { it == '"' || it == '\'' }
    if (quoteIdx > 0) s = s.substring(quoteIdx)
    for (q in listOf("\"\"\"", "'''")) {
        if (s.length >= 6 && s.startsWith(q) && s.endsWith(q)) return s.substring(3, s.length - 3)
    }
    if (s.length >= 2 && (s.first() == '"' || s.first() == '\'') && s.last() == s.first()) {
        return s.substring(1, s.length - 1)
    }
    return s
}
