package org.opentaint.semgrep.go.pattern.conversion

import org.opentaint.semgrep.go.pattern.ConcreteName
import org.opentaint.semgrep.go.pattern.Identifier
import org.opentaint.semgrep.go.pattern.ImportDecl
import org.opentaint.semgrep.go.pattern.ParsedImportDecl
import org.opentaint.semgrep.go.pattern.QualifiedIdent
import org.opentaint.semgrep.go.pattern.QualifiedType
import org.opentaint.semgrep.go.pattern.RemovedImportDecl
import org.opentaint.semgrep.go.pattern.SemgrepGoPattern
import org.opentaint.semgrep.go.pattern.StringLiteral
import org.opentaint.semgrep.go.pattern.TypeName
import org.opentaint.semgrep.pattern.NormalizedSemgrepRule

object GoImportRewriter {

    fun rewriteImports(
        pattern: NormalizedSemgrepRule<SemgrepGoPattern>
    ): List<NormalizedSemgrepRule<SemgrepGoPattern>> {
        val decls = mutableListOf<ParsedImportDecl>()

        val importRemover = object : GoPatternRewriter {
            override fun ParsedImportDecl.rewriteParsedImportDecl(): List<ImportDecl> {
                decls += this
                return listOf(RemovedImportDecl)
            }
        }

        val patternWithoutImports = importRemover.safeRewrite(pattern) {
            error("Rewrite exceptions are not expected here")
        }

        if (decls.isEmpty()) return listOf(pattern)

        val importSelectorMap = buildSelectorMap(decls)
            ?: return listOf(pattern)

        val importQualifier = object : GoPatternRewriter {
            override fun rewriteQualifiedType(type: QualifiedType): TypeName {
                val full = (type.pkg as? ConcreteName)?.name?.let { importSelectorMap[it] }
                if (full == null) return super.rewriteQualifiedType(type)

                val name = type.name.rewriteName()
                val args = type.typeArgs.map { it.rewriteTypeName() }
                return QualifiedType(ConcreteName(full), name, args)
            }

            override fun rewriteSelectorInstance(obj: SemgrepGoPattern): List<SemgrepGoPattern> {
                val name = obj.selectorConcreteName()
                val full = name?.let { importSelectorMap[it] }
                if (full == null) return super.rewriteSelectorInstance(obj)

                return listOf(Identifier(ConcreteName(full)))
            }

            private fun SemgrepGoPattern.selectorConcreteName(): String? {
                if (this !is Identifier) return null
                return (name as? ConcreteName)?.name
            }

            override fun rewriteQualifiedIdent(ident: QualifiedIdent): List<SemgrepGoPattern> {
                val full = (ident.pkg as? ConcreteName)?.name?.let { importSelectorMap[it] }
                if (full == null) return super.rewriteQualifiedIdent(ident)

                val sel = ident.sel.rewriteName()
                return listOf(QualifiedIdent(ConcreteName(full), sel))
            }
        }

        return patternWithoutImports.flatMap {
            importQualifier.safeRewrite(it){
                error("Rewrite exceptions are not expected here")
            }
        }
    }

    private fun buildSelectorMap(imports: List<ParsedImportDecl>): Map<String, String>? {
        val map = hashMapOf<String, String>()
        for (decl in imports) {
            for (spec in decl.specs) {
                if (spec.dotImport) return null

                val path = (spec.path as? StringLiteral)?.let { (it.content as? ConcreteName)?.name }
                    ?: return null

                val selector = (spec.alias as? ConcreteName)?.name ?: path.substringAfterLast('/')

                val old = map.putIfAbsent(selector, path)
                if (old != null && old != path) {
                    return null
                }
            }
        }
        return map
    }
}
