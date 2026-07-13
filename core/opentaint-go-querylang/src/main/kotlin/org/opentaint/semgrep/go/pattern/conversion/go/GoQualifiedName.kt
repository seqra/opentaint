package org.opentaint.semgrep.go.pattern.conversion.go

import org.opentaint.semgrep.go.pattern.conversion.GoConcreteType
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.SignatureName
import org.opentaint.semgrep.pattern.conversion.TypeConstraint

/**
 * Build the qualified Go function name as used to identify a function for taint rules
 * (e.g. "pkg.Func", "T.Method", "(*T).Method"), or null if the call cannot be concretely named
 * (metavar/any method name, or a metavar receiver/enclosing type).
 *
 * Note: this uses the package SELECTOR from the pattern (e.g. "util"), which matches the Go IR's
 * function name only when the package import path equals that selector. Bridging selector->import-path
 * is out of v1 scope; the end-to-end test arranges samples accordingly.
 */
fun goQualifiedName(methodName: SignatureName, enclosing: TypeConstraint?): String? {
    val name = (methodName as? SignatureName.Concrete)?.name ?: return null
    return when (val e = enclosing) {
        null, TypeConstraint.Any -> name
        is TypeConstraint.MetaVar -> null
        is TypeConstraint.Concrete -> when (val t = e.type) {
            is GoConcreteType.Qualified -> "${t.pkg}.$name"
            is GoConcreteType.Named -> "${t.name}.$name"
            is GoConcreteType.Pointer -> {
                val inner = t.elem
                if (inner is TypeConstraint.Concrete) {
                    when (val it2 = inner.type) {
                        is GoConcreteType.Named -> "(*${it2.name}).$name"
                        is GoConcreteType.Qualified -> "(*${it2.pkg}.${it2.name}).$name"
                        else -> null
                    }
                } else null
            }
            else -> null
        }
    }
}
