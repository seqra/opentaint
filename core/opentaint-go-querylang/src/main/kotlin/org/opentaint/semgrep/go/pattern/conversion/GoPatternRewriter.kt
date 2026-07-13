package org.opentaint.semgrep.go.pattern.conversion

import org.opentaint.semgrep.go.pattern.ArgPrefix
import org.opentaint.semgrep.go.pattern.ArrayType
import org.opentaint.semgrep.go.pattern.AssignStmt
import org.opentaint.semgrep.go.pattern.BinaryExpr
import org.opentaint.semgrep.go.pattern.BlockStmt
import org.opentaint.semgrep.go.pattern.BoolConstant
import org.opentaint.semgrep.go.pattern.BranchStmt
import org.opentaint.semgrep.go.pattern.CallArgs
import org.opentaint.semgrep.go.pattern.CallExpr
import org.opentaint.semgrep.go.pattern.CaseClause
import org.opentaint.semgrep.go.pattern.CaseValues
import org.opentaint.semgrep.go.pattern.ChanType
import org.opentaint.semgrep.go.pattern.CommCase
import org.opentaint.semgrep.go.pattern.CommClause
import org.opentaint.semgrep.go.pattern.CommDefault
import org.opentaint.semgrep.go.pattern.CommEllipsis
import org.opentaint.semgrep.go.pattern.CommRecv
import org.opentaint.semgrep.go.pattern.CommSend
import org.opentaint.semgrep.go.pattern.CompositeElem
import org.opentaint.semgrep.go.pattern.CompositeLit
import org.opentaint.semgrep.go.pattern.ConcreteName
import org.opentaint.semgrep.go.pattern.ConstDecl
import org.opentaint.semgrep.go.pattern.ConversionExpr
import org.opentaint.semgrep.go.pattern.DeepExpr
import org.opentaint.semgrep.go.pattern.DefaultCase
import org.opentaint.semgrep.go.pattern.DeferStmt
import org.opentaint.semgrep.go.pattern.Ellipsis
import org.opentaint.semgrep.go.pattern.EllipsisArgPrefix
import org.opentaint.semgrep.go.pattern.EllipsisCase
import org.opentaint.semgrep.go.pattern.EllipsisElem
import org.opentaint.semgrep.go.pattern.EllipsisField
import org.opentaint.semgrep.go.pattern.EllipsisInterfaceElem
import org.opentaint.semgrep.go.pattern.EllipsisMetavar
import org.opentaint.semgrep.go.pattern.EllipsisMetavarParam
import org.opentaint.semgrep.go.pattern.EllipsisParam
import org.opentaint.semgrep.go.pattern.EllipsisStmt
import org.opentaint.semgrep.go.pattern.EllipsisType
import org.opentaint.semgrep.go.pattern.EmbeddedType
import org.opentaint.semgrep.go.pattern.ExprCaseValues
import org.opentaint.semgrep.go.pattern.ExprStmt
import org.opentaint.semgrep.go.pattern.FieldDecl
import org.opentaint.semgrep.go.pattern.FloatLiteral
import org.opentaint.semgrep.go.pattern.ForEllipsisStmt
import org.opentaint.semgrep.go.pattern.ForStmt
import org.opentaint.semgrep.go.pattern.FuncDecl
import org.opentaint.semgrep.go.pattern.FuncLit
import org.opentaint.semgrep.go.pattern.FuncType
import org.opentaint.semgrep.go.pattern.GoStmt
import org.opentaint.semgrep.go.pattern.Identifier
import org.opentaint.semgrep.go.pattern.IfStmt
import org.opentaint.semgrep.go.pattern.ImaginaryLiteral
import org.opentaint.semgrep.go.pattern.ImportDecl
import org.opentaint.semgrep.go.pattern.ImportSpec
import org.opentaint.semgrep.go.pattern.IncDecStmt
import org.opentaint.semgrep.go.pattern.IndexExpr
import org.opentaint.semgrep.go.pattern.IntLiteral
import org.opentaint.semgrep.go.pattern.InterfaceElem
import org.opentaint.semgrep.go.pattern.InterfaceType
import org.opentaint.semgrep.go.pattern.KeyedElem
import org.opentaint.semgrep.go.pattern.LabeledStmt
import org.opentaint.semgrep.go.pattern.MapType
import org.opentaint.semgrep.go.pattern.Metavar
import org.opentaint.semgrep.go.pattern.MetavarName
import org.opentaint.semgrep.go.pattern.MetavarParam
import org.opentaint.semgrep.go.pattern.MetavarType
import org.opentaint.semgrep.go.pattern.MethodDecl
import org.opentaint.semgrep.go.pattern.MethodSpec
import org.opentaint.semgrep.go.pattern.Name
import org.opentaint.semgrep.go.pattern.NamedFieldDecl
import org.opentaint.semgrep.go.pattern.NamedParam
import org.opentaint.semgrep.go.pattern.NamedType
import org.opentaint.semgrep.go.pattern.NilLiteral
import org.opentaint.semgrep.go.pattern.NoArgs
import org.opentaint.semgrep.go.pattern.PackageClause
import org.opentaint.semgrep.go.pattern.PackageOnlyPattern
import org.opentaint.semgrep.go.pattern.ParameterDecl
import org.opentaint.semgrep.go.pattern.ParsedImportDecl
import org.opentaint.semgrep.go.pattern.PointerType
import org.opentaint.semgrep.go.pattern.QualifiedIdent
import org.opentaint.semgrep.go.pattern.QualifiedType
import org.opentaint.semgrep.go.pattern.RangeStmt
import org.opentaint.semgrep.go.pattern.RecvStmt
import org.opentaint.semgrep.go.pattern.RemovedImportDecl
import org.opentaint.semgrep.go.pattern.ReturnStmt
import org.opentaint.semgrep.go.pattern.RuneLiteral
import org.opentaint.semgrep.go.pattern.SelectStmt
import org.opentaint.semgrep.go.pattern.SelectorExpr
import org.opentaint.semgrep.go.pattern.SemgrepGoPattern
import org.opentaint.semgrep.go.pattern.SendStmt
import org.opentaint.semgrep.go.pattern.ShortVarDecl
import org.opentaint.semgrep.go.pattern.SliceExpr
import org.opentaint.semgrep.go.pattern.SliceType
import org.opentaint.semgrep.go.pattern.SourceFile
import org.opentaint.semgrep.go.pattern.StarExpr
import org.opentaint.semgrep.go.pattern.StringEllipsis
import org.opentaint.semgrep.go.pattern.StringLiteral
import org.opentaint.semgrep.go.pattern.StructType
import org.opentaint.semgrep.go.pattern.SwitchStmt
import org.opentaint.semgrep.go.pattern.TopList
import org.opentaint.semgrep.go.pattern.TypeAssertion
import org.opentaint.semgrep.go.pattern.TypeCaseClause
import org.opentaint.semgrep.go.pattern.TypeCaseValuesList
import org.opentaint.semgrep.go.pattern.TypeDecl
import org.opentaint.semgrep.go.pattern.TypeName
import org.opentaint.semgrep.go.pattern.TypeOnlyPattern
import org.opentaint.semgrep.go.pattern.TypeSpec
import org.opentaint.semgrep.go.pattern.TypeSwitchStmt
import org.opentaint.semgrep.go.pattern.TypedMetavar
import org.opentaint.semgrep.go.pattern.UnaryExpr
import org.opentaint.semgrep.go.pattern.ValueSpec
import org.opentaint.semgrep.go.pattern.VarDecl
import org.opentaint.semgrep.pattern.NormalizedSemgrepRule
import org.opentaint.semgrep.pattern.conversion.cartesianProductMapTo

interface GoPatternRewriter {
    fun SemgrepGoPattern.rewrite(): List<SemgrepGoPattern> = when (this) {
        is SemgrepGoPattern.Raw -> listOf(this)
        is Metavar -> listOf(this)
        is EllipsisMetavar -> listOf(this)
        Ellipsis -> listOf(Ellipsis)
        is DeepExpr -> nested.rewrite().map(::DeepExpr)
        is TypedMetavar -> listOf(TypedMetavar(name, type.rewriteTypeName()))
        is Identifier -> listOf(Identifier(name.rewriteName()))
        is QualifiedIdent -> rewriteQualifiedIdent(this)
        is IntLiteral -> listOf(this)
        is FloatLiteral -> listOf(this)
        is ImaginaryLiteral -> listOf(this)
        is RuneLiteral -> listOf(this)
        is BoolConstant -> listOf(this)
        NilLiteral -> listOf(NilLiteral)
        is StringLiteral -> listOf(StringLiteral(content.rewriteName()))
        StringEllipsis -> listOf(StringEllipsis)
        is CallArgs -> rewriteCallArgs()
        is CallExpr -> rewriteCallExpr()
        is SelectorExpr -> rewriteSelectorExpr()
        is IndexExpr -> rewriteBinary(obj, index, ::IndexExpr)
        is SliceExpr -> rewriteSliceExpr()
        is TypeAssertion -> obj.rewrite().map { TypeAssertion(it, type?.rewriteTypeName()) }
        is BinaryExpr -> rewriteBinary(left, right) { newLeft, newRight -> BinaryExpr(op, newLeft, newRight) }
        is UnaryExpr -> operand.rewrite().map { UnaryExpr(op, it) }
        is StarExpr -> operand.rewrite().map(::StarExpr)
        is CompositeElem -> rewriteCompositeElem()
        is CompositeLit -> elements.rewriteCompositeElems().map { CompositeLit(type?.rewriteTypeName(), it) }
        is FuncLit -> body.rewriteBlockStmts().map { FuncLit(signature.rewriteFuncType(), it) }
        is ConversionExpr -> expr.rewrite().map { ConversionExpr(type.rewriteTypeName(), it) }
        is BlockStmt -> rewriteBlockStmts()
        is IfStmt -> rewriteIfStmt()
        is ForStmt -> rewriteForStmt()
        is ForEllipsisStmt -> body.rewriteBlockStmts().map(::ForEllipsisStmt)
        is RangeStmt -> rewriteRangeStmt()
        is CaseClause -> rewriteCaseClause()
        is TypeCaseClause -> rewriteTypeCaseClause()
        is CommClause -> rewriteCommClause()
        is SwitchStmt -> rewriteSwitchStmt()
        is TypeSwitchStmt -> rewriteTypeSwitchStmt()
        is SelectStmt -> cases.rewriteCommClauses().map(::SelectStmt)
        is ReturnStmt -> values.rewritePatterns().map(::ReturnStmt)
        is DeferStmt -> call.rewrite().map(::DeferStmt)
        is GoStmt -> call.rewrite().map(::GoStmt)
        is AssignStmt -> rewriteAssignStmt()
        is ShortVarDecl -> rewriteShortVarDecl()
        is IncDecStmt -> operand.rewrite().map { IncDecStmt(it, op) }
        is SendStmt -> rewriteBinary(channel, value, ::SendStmt)
        is RecvStmt -> rewriteRecvStmt()
        is LabeledStmt -> rewriteOptionalPattern(stmt).map { LabeledStmt(label.rewriteName(), it) }
        is BranchStmt -> listOf(BranchStmt(kind, label?.rewriteName()))
        is ExprStmt -> expr.rewrite().map(::ExprStmt)
        EllipsisStmt -> listOf(EllipsisStmt)
        is PackageClause -> listOf(PackageClause(name.rewriteName()))
        is ImportSpec -> path.rewrite().map { ImportSpec(alias?.rewriteName(), dotImport, it) }
        is ImportDecl -> rewriteImportDecl()
        is ValueSpec -> values.rewritePatterns().map { ValueSpec(names.map { name -> name.rewriteName() }, type?.rewriteTypeName(), it) }
        is ConstDecl -> specs.rewriteValueSpecs().map(::ConstDecl)
        is VarDecl -> specs.rewriteValueSpecs().map(::VarDecl)
        is TypeSpec -> listOf(TypeSpec(name.rewriteName(), alias, type.rewriteTypeName()))
        is TypeDecl -> listOf(TypeDecl(specs.map { it.rewriteTypeSpec() }))
        is FuncDecl -> rewriteFuncDecl()
        is MethodDecl -> rewriteMethodDecl()
        is ParameterDecl -> rewriteParameterDecl()
        is FieldDecl -> rewriteFieldDecl()
        is PackageOnlyPattern -> pkg.rewrite().map { PackageOnlyPattern(it as PackageClause) }
        is TypeOnlyPattern -> listOf(TypeOnlyPattern(type.rewriteTypeName()))
        is TopList -> items.rewritePatterns().map(::TopList)
        is SourceFile -> rewriteSourceFile()
    }

    fun rewriteQualifiedIdent(ident: QualifiedIdent): List<SemgrepGoPattern> =
        listOf(QualifiedIdent(ident.pkg.rewriteName(), ident.sel.rewriteName()))

    fun CallArgs.rewriteCallArgs(): List<CallArgs> = when (this) {
        NoArgs -> listOf(NoArgs)
        is EllipsisArgPrefix -> rest.rewriteCallArgs().map(::EllipsisArgPrefix)
        is ArgPrefix -> {
            val newArgs = arg.rewrite()
            val newRests = rest.rewriteCallArgs()
            newArgs.flatMap { newArg -> newRests.map { ArgPrefix(newArg, it) } }
        }
    }

    fun CallExpr.rewriteCallExpr(): List<SemgrepGoPattern> {
        val newFns = fn.rewrite()
        val newArgs = args.rewriteCallArgs()
        return newFns.flatMap { newFn -> newArgs.map { CallExpr(newFn, it, hasEllipsis) } }
    }

    fun SliceExpr.rewriteSliceExpr(): List<SemgrepGoPattern> {
        val newObjs = obj.rewrite()
        val newLows = rewriteOptionalPattern(low)
        val newHighs = rewriteOptionalPattern(high)
        val newMaxes = rewriteOptionalPattern(max)
        return newObjs.flatMap { newObj ->
            newLows.flatMap { newLow ->
                newHighs.flatMap { newHigh ->
                    newMaxes.map { newMax -> SliceExpr(newObj, newLow, newHigh, newMax) }
                }
            }
        }
    }

    fun SelectorExpr.rewriteSelectorExpr(): List<SemgrepGoPattern> =
        rewriteSelectorInstance(obj).map { SelectorExpr(it, sel.rewriteName()) }

    fun rewriteSelectorInstance(obj: SemgrepGoPattern): List<SemgrepGoPattern> = obj.rewrite()

    fun CompositeElem.rewriteCompositeElem(): List<CompositeElem> = when (this) {
        EllipsisElem -> listOf(EllipsisElem)
        is KeyedElem -> {
            val newKeys = rewriteOptionalPattern(key)
            val newValues = value.rewrite()
            newKeys.flatMap { newKey -> newValues.map { KeyedElem(newKey, it) } }
        }
    }

    fun BlockStmt.rewriteBlockStmts(): List<BlockStmt> = stmts.rewritePatterns().map(::BlockStmt)

    fun IfStmt.rewriteIfStmt(): List<SemgrepGoPattern> {
        val newInits = rewriteOptionalPattern(init)
        val newConds = cond.rewrite()
        val newThens = then.rewriteBlockStmts()
        val newEls = rewriteOptionalPattern(els)
        return newInits.flatMap { newInit ->
            newConds.flatMap { newCond ->
                newThens.flatMap { newThen ->
                    newEls.map { newElse -> IfStmt(newInit, newCond, newThen, newElse) }
                }
            }
        }
    }

    fun ForStmt.rewriteForStmt(): List<SemgrepGoPattern> {
        val newInits = rewriteOptionalPattern(init)
        val newConds = rewriteOptionalPattern(cond)
        val newPosts = rewriteOptionalPattern(post)
        val newBodies = body.rewriteBlockStmts()
        return newInits.flatMap { newInit ->
            newConds.flatMap { newCond ->
                newPosts.flatMap { newPost ->
                    newBodies.map { ForStmt(newInit, newCond, newPost, it) }
                }
            }
        }
    }

    fun RangeStmt.rewriteRangeStmt(): List<SemgrepGoPattern> {
        val newKeys = rewriteOptionalPattern(key)
        val newValues = rewriteOptionalPattern(value)
        val newRanges = range.rewrite()
        val newBodies = body.rewriteBlockStmts()
        return newKeys.flatMap { newKey ->
            newValues.flatMap { newValue ->
                newRanges.flatMap { newRange ->
                    newBodies.map { RangeStmt(newKey, newValue, decl, newRange, it) }
                }
            }
        }
    }

    fun CaseClause.rewriteCaseClause(): List<SemgrepGoPattern> =
        body.rewritePatterns().map { CaseClause(values.rewriteCaseValues(), it) }

    fun TypeCaseClause.rewriteTypeCaseClause(): List<SemgrepGoPattern> =
        body.rewritePatterns().map { TypeCaseClause(values.rewriteCaseValues(), it) }

    fun CommClause.rewriteCommClause(): List<SemgrepGoPattern> {
        val newComms = comm.rewriteCommCase()
        val newBodies = body.rewritePatterns()
        return newComms.flatMap { newComm -> newBodies.map { CommClause(newComm, it) } }
    }

    fun SwitchStmt.rewriteSwitchStmt(): List<SemgrepGoPattern> {
        val newInits = rewriteOptionalPattern(init)
        val newTags = rewriteOptionalPattern(tag)
        val newCases = cases.rewriteCaseClauses()
        return newInits.flatMap { newInit ->
            newTags.flatMap { newTag ->
                newCases.map { SwitchStmt(newInit, newTag, it) }
            }
        }
    }

    fun TypeSwitchStmt.rewriteTypeSwitchStmt(): List<SemgrepGoPattern> {
        val newInits = rewriteOptionalPattern(init)
        val newGuards = guard.rewrite()
        val newCases = cases.rewriteTypeCaseClauses()
        return newInits.flatMap { newInit ->
            newGuards.flatMap { newGuard ->
                newCases.map { TypeSwitchStmt(newInit, newGuard, it) }
            }
        }
    }

    fun AssignStmt.rewriteAssignStmt(): List<SemgrepGoPattern> {
        val newLhs = lhs.rewritePatterns()
        val newRhs = rhs.rewritePatterns()
        return newLhs.flatMap { lhs -> newRhs.map { AssignStmt(op, lhs, it) } }
    }

    fun ShortVarDecl.rewriteShortVarDecl(): List<SemgrepGoPattern> {
        val newLhs = lhs.rewritePatterns()
        val newRhs = rhs.rewritePatterns()
        return newLhs.flatMap { lhs -> newRhs.map { ShortVarDecl(lhs, it) } }
    }

    fun RecvStmt.rewriteRecvStmt(): List<SemgrepGoPattern> {
        val newLhs = lhs.rewritePatterns()
        val newValues = value.rewrite()
        return newLhs.flatMap { lhs -> newValues.map { RecvStmt(lhs, op, it) } }
    }

    fun FuncDecl.rewriteFuncDecl(): List<SemgrepGoPattern> =
        rewriteOptionalBlock(body).map { FuncDecl(name.rewriteName(), signature.rewriteFuncType(), it) }

    fun MethodDecl.rewriteMethodDecl(): List<SemgrepGoPattern> {
        val newReceivers = receiver.rewriteParameterDecl()
        val newBodies = rewriteOptionalBlock(body)
        return newReceivers.flatMap { newReceiver ->
            newBodies.map { MethodDecl(newReceiver, name.rewriteName(), signature.rewriteFuncType(), it) }
        }
    }

    fun ParameterDecl.rewriteParameterDecl(): List<ParameterDecl> = when (this) {
        is NamedParam -> listOf(NamedParam(names.map { name -> name.rewriteName() }, type.rewriteTypeName(), variadic))
        EllipsisParam -> listOf(EllipsisParam)
        is EllipsisMetavarParam -> listOf(this)
        is MetavarParam -> listOf(this)
    }

    fun FieldDecl.rewriteFieldDecl(): List<FieldDecl> = when (this) {
        is NamedFieldDecl -> listOf(
            NamedFieldDecl(
                names = names.map { name -> name.rewriteName() },
                type = type?.rewriteTypeName(),
                embedded = embedded?.rewriteTypeName(),
                tag = tag,
            )
        )
        EllipsisField -> listOf(EllipsisField)
    }

    fun SourceFile.rewriteSourceFile(): List<SemgrepGoPattern> {
        val newPkgs = pkg.rewrite().map { it as PackageClause }
        val newImports = imports.rewriteImportDecls()
        val newDecls = decls.rewritePatterns()
        return newPkgs.flatMap { newPkg ->
            newImports.flatMap { newImports ->
                newDecls.map { SourceFile(newPkg, newImports, it) }
            }
        }
    }

    fun TypeName.rewriteTypeName(): TypeName = when (this) {
        is NamedType -> NamedType(name.rewriteName(), typeArgs.map { it.rewriteTypeName() })
        is QualifiedType -> rewriteQualifiedType(this)
        is PointerType -> PointerType(elem.rewriteTypeName())
        is SliceType -> SliceType(elem.rewriteTypeName())
        is ArrayType -> ArrayType(len?.rewrite()?.singleOrNull() ?: len, elem.rewriteTypeName())
        is MapType -> MapType(key.rewriteTypeName(), value.rewriteTypeName())
        is ChanType -> ChanType(dir, elem.rewriteTypeName())
        is FuncType -> rewriteFuncType()
        is StructType -> StructType(fields.map { it.rewriteFieldDecl().single() })
        is InterfaceType -> InterfaceType(methods.map { it.rewriteInterfaceElem() })
        EllipsisType -> EllipsisType
        is MetavarType -> this
    }

    fun rewriteQualifiedType(type: QualifiedType): TypeName =
        QualifiedType(type.pkg.rewriteName(), type.name.rewriteName(), type.typeArgs.map { it.rewriteTypeName() })

    fun FuncType.rewriteFuncType(): FuncType = FuncType(
        params = params.map { it.rewriteParameterDecl().single() },
        results = results.map { it.rewriteParameterDecl().single() },
    )

    fun InterfaceElem.rewriteInterfaceElem(): InterfaceElem = when (this) {
        is MethodSpec -> MethodSpec(name.rewriteName(), signature.rewriteFuncType())
        is EmbeddedType -> EmbeddedType(type.rewriteTypeName())
        EllipsisInterfaceElem -> EllipsisInterfaceElem
    }

    fun Name.rewriteName(): Name = when (this) {
        is ConcreteName -> this
        is MetavarName -> this
    }

    fun CaseValues.rewriteCaseValues(): CaseValues = when (this) {
        DefaultCase -> DefaultCase
        is ExprCaseValues -> ExprCaseValues(exprs.flatMap { it.rewrite() })
        is TypeCaseValuesList -> TypeCaseValuesList(types.map { it.rewriteTypeName() })
        EllipsisCase -> EllipsisCase
    }

    fun CommCase.rewriteCommCase(): List<CommCase> = when (this) {
        CommDefault -> listOf(CommDefault)
        is CommSend -> stmt.rewrite().map { CommSend(it as SendStmt) }
        is CommRecv -> stmt.rewrite().map { CommRecv(it as RecvStmt) }
        CommEllipsis -> listOf(CommEllipsis)
    }

    fun TypeSpec.rewriteTypeSpec(): TypeSpec = TypeSpec(name.rewriteName(), alias, type.rewriteTypeName())

    fun rewriteOptionalPattern(pattern: SemgrepGoPattern?): List<SemgrepGoPattern?> = pattern?.rewrite() ?: listOf(null)

    fun rewriteOptionalBlock(block: BlockStmt?): List<BlockStmt?> = block?.rewriteBlockStmts() ?: listOf(null)

    fun List<SemgrepGoPattern>.rewritePatterns(): List<List<SemgrepGoPattern>> =
        map { it.rewrite() }.cartesianProductMapTo { it.toList() }

    fun List<CompositeElem>.rewriteCompositeElems(): List<List<CompositeElem>> =
        map { it.rewriteCompositeElem() }.cartesianProductMapTo { it.toList() }

    fun List<CaseClause>.rewriteCaseClauses(): List<List<CaseClause>> =
        map { it.rewriteCaseClause().map { pattern -> pattern as CaseClause } }.cartesianProductMapTo { it.toList() }

    fun List<TypeCaseClause>.rewriteTypeCaseClauses(): List<List<TypeCaseClause>> =
        map { it.rewriteTypeCaseClause().map { pattern -> pattern as TypeCaseClause } }.cartesianProductMapTo { it.toList() }

    fun List<CommClause>.rewriteCommClauses(): List<List<CommClause>> =
        map { it.rewriteCommClause().map { pattern -> pattern as CommClause } }.cartesianProductMapTo { it.toList() }

    fun List<ImportSpec>.rewriteImportSpecs(): List<List<ImportSpec>> =
        map { spec -> spec.rewrite().map { it as ImportSpec } }.cartesianProductMapTo { it.toList() }

    fun List<ImportDecl>.rewriteImportDecls(): List<List<ImportDecl>> =
        map { decl -> decl.rewriteImportDecl() }.cartesianProductMapTo { it.toList() }

    fun ImportDecl.rewriteImportDecl(): List<ImportDecl> = when (this) {
        is ParsedImportDecl -> rewriteParsedImportDecl()
        is RemovedImportDecl -> listOf(this)
    }

    fun ParsedImportDecl.rewriteParsedImportDecl(): List<ImportDecl> =
        specs.rewriteImportSpecs().map { ParsedImportDecl(it, hasEllipsis) }

    fun List<ValueSpec>.rewriteValueSpecs(): List<List<ValueSpec>> =
        map { spec -> spec.rewrite().map { it as ValueSpec } }.cartesianProductMapTo { it.toList() }

    fun rewriteBinary(
        left: SemgrepGoPattern,
        right: SemgrepGoPattern,
        create: (SemgrepGoPattern, SemgrepGoPattern) -> SemgrepGoPattern,
    ): List<SemgrepGoPattern> {
        val newLefts = left.rewrite()
        val newRights = right.rewrite()
        return newLefts.flatMap { newLeft -> newRights.map { create(newLeft, it) } }
    }
}

open class GoRewriteException(message: String) : Exception(message) {
    override fun fillInStackTrace(): Throwable = this
}

inline fun GoPatternRewriter.safeRewrite(
    pattern: SemgrepGoPattern,
    onException: (GoRewriteException) -> Nothing,
): List<SemgrepGoPattern> = try {
    pattern.rewrite()
} catch (ex: GoRewriteException) {
    onException(ex)
}

inline fun GoPatternRewriter.safeRewrite(
    rule: NormalizedSemgrepRule<SemgrepGoPattern>,
    onException: (GoRewriteException) -> Nothing,
): List<NormalizedSemgrepRule<SemgrepGoPattern>> {
    val newPatternsOptions = rule.patterns
        .map { safeRewrite(it, onException) }
        .cartesianProductMapTo { it.toList() }

    val newPatternInsidesOptions = rule.patternInsides
        .map { safeRewrite(it, onException) }
        .cartesianProductMapTo { it.toList() }

    val newPatternNots = rule.patternNots
        .flatMap { safeRewrite(it, onException) }

    val newPatternNotInsides = rule.patternNotInsides
        .flatMap { safeRewrite(it, onException) }

    return newPatternsOptions.flatMap { newPatterns ->
        newPatternInsidesOptions.map { newPatternInsides ->
            NormalizedSemgrepRule(
                patterns = newPatterns,
                patternNots = newPatternNots,
                patternInsides = newPatternInsides,
                patternNotInsides = newPatternNotInsides,
            )
        }
    }
}
