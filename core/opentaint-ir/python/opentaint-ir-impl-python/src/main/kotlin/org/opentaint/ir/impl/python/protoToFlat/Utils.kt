package org.opentaint.ir.impl.python.protoToFlat

import org.opentaint.ir.impl.python.proto.MypyImportFromStmtProto
import org.opentaint.ir.impl.python.proto.MypyImportStmtProto
import org.opentaint.ir.impl.python.proto.MypyMemberExprProto
import org.opentaint.ir.impl.python.proto.MypyNameExprProto

internal fun recordImports(importManager: ImportManager, stmt: MypyImportStmtProto) {
    for (id in stmt.idsList) importManager.recordImport(id.module, id.alias)
}

internal fun recordImportsFrom(importManager: ImportManager, stmt: MypyImportFromStmtProto) {
    for (name in stmt.namesList) importManager.recordImportFrom(stmt.module, name.name, name.alias)
}

internal fun ImportManager.qualify(expr: MypyNameExprProto): String? =
    resolve(expr.name)?.dottedName() ?: expr.fullname.ifEmpty { null }

internal fun ImportManager.dottedPath(me: MypyMemberExprProto): String {
    val prefix = when {
        me.expr.hasNameExpr() -> qualify(me.expr.nameExpr) ?: me.expr.nameExpr.name
        me.expr.hasMemberExpr() -> dottedPath(me.expr.memberExpr)
        else -> "<expr>"
    }
    return "$prefix.${me.name}"
}

private fun ImportBinding.dottedName(): String = when (this) {
    is ImportBinding.Module -> name
    is ImportBinding.Attr -> "${parent.dottedName()}.$name"
}
