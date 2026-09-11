package org.opentaint.ir.impl.python.transforms.closure

import org.opentaint.ir.api.python.PIRDiagnostic
import org.opentaint.ir.api.python.PIRDiagnosticSeverity
import org.opentaint.ir.impl.python.flat.FlatClass
import org.opentaint.ir.impl.python.flat.FlatFunctionIR
import org.opentaint.ir.impl.python.flat.FlatLocal
import org.opentaint.ir.impl.python.flat.FlatModuleIR
import org.opentaint.ir.impl.python.flat.FlatValue
import org.opentaint.ir.impl.python.flat.operands
import org.opentaint.ir.impl.python.flat.targets
import kotlin.collections.orEmpty

data class ClosureAnalysis(
    val info: Map<String, ClosureInfo>,
    val diagnostics: List<PIRDiagnostic>,
)

class ClosureAnalyzer private constructor(val module: FlatModuleIR) {
    private val byName: Map<String, FlatFunctionIR> = collectAllFunctions(module).associateBy { it.qualifiedName }
    private val publicCache = HashMap<String, ClosureInfo>()
    private val parentMap: Map<String, String?> = buildClosureParentMap(module, byName)
    private val children: Map<String, List<String>> = buildChildrenMap(parentMap)

    private val propagatedClosureVars = HashMap<String, Set<String>>()
    private val diagnostics = ArrayList<PIRDiagnostic>()

    private fun analyze(): ClosureAnalysis {
        for (qn in byName.keys) compute(qn)
        pruneUnprovidableClosureVars()
        return ClosureAnalysis(info = publicCache, diagnostics = diagnostics)
    }

    private fun pruneUnprovidableClosureVars() {
        fun prune(qn: String) {
            parentMap[qn]?.let { parentQn ->
                val parent = publicCache.getValue(parentQn)
                val provided = parent.cellVars + parent.closureVars
                val ci = publicCache.getValue(qn)
                val kept = ci.closureVars.filterTo(LinkedHashSet()) { it in provided }
                if (kept.size != ci.closureVars.size) publicCache[qn] = ci.copy(closureVars = kept)
            }
            for (child in children[qn].orEmpty()) prune(child)
        }
        for (qn in byName.keys) if (parentMap[qn] == null) prune(qn)
    }

    private fun compute(qn: String): ClosureInfo = publicCache.getOrPut(qn) {
        val fn = byName.getValue(qn)

        val params = fn.parameters.map { it.name }.toSet()
        val localDefs = collectLocalDefs(fn)
        val refs = collectLocalReads(fn)

        val nonlocal = fn.nonlocalNames
        val global = fn.globalNames

        val trueLocals = localDefs - nonlocal - global
        val ownedNames = (params + trueLocals).filterNot(::isSynthetic).toSet()

        val directFree =
            ((refs - ownedNames - global).filterNot(::isSynthetic).toSet()) +
                    nonlocal

        val childQns = children[qn].orEmpty()
        for (childQn in childQns) compute(childQn)
        val childNeeds: Set<String> = childQns
            .flatMap { propagatedClosureVars.getValue(it) }
            .toSet()

        val cellVars = (childNeeds intersect ownedNames).sortedDeterministic()
        val propagated = (directFree + (childNeeds - ownedNames)).sortedDeterministic()
        propagatedClosureVars[qn] = propagated

        val isClosureRoot = parentMap[qn] == null
        if (isClosureRoot && propagated.isNotEmpty()) {
            diagnostics.add(
                PIRDiagnostic(
                    severity = PIRDiagnosticSeverity.WARNING,
                    message = "Closure-root '$qn' has free names ${propagated.toSortedSet()} " +
                            "owned by no enclosing scope; read as globals/unresolved locals.",
                    functionName = qn,
                    exceptionType = "ClosureRootLeak",
                ),
            )
        }
        val publicClosureVars = if (isClosureRoot) emptySet() else propagated

        ClosureInfo(
            ownedNames = ownedNames.sortedDeterministic(),
            cellVars = cellVars,
            closureVars = publicClosureVars,
            isClosureRoot = isClosureRoot,
        )
    }

    private fun isSynthetic(name: String): Boolean =
        name.contains('$') || name.contains('<') || name.contains('>')

    private fun Set<String>.sortedDeterministic(): Set<String> =
        if (size <= 1) this else LinkedHashSet<String>(size).also { dst ->
            for (s in this.sorted()) dst.add(s)
        }

    private fun collectAllFunctions(module: FlatModuleIR): List<FlatFunctionIR> {
        val out = ArrayList<FlatFunctionIR>()
        out.add(module.moduleInit)
        out.addAll(module.functions)
        for (cls in module.classes) collectClassFunctions(cls, out)
        return out
    }

    private fun collectClassFunctions(cls: FlatClass, out: MutableList<FlatFunctionIR>) {
        out.addAll(cls.methods)
        for (nested in cls.nestedClasses) collectClassFunctions(nested, out)
    }

    private fun buildClosureParentMap(
        module: FlatModuleIR,
        byName: Map<String, FlatFunctionIR>,
    ): Map<String, String?> {
        val map = HashMap<String, String?>()

        map[module.moduleInit.qualifiedName] = null

        for (fn in module.functions) {
            map[fn.qualifiedName] = fn.parentQualifiedName
        }

        for (cls in module.classes) walkClass(cls, enclosingFunction = null, map = map)

        return map.mapValues { (_, parent) -> if (parent != null && parent in byName) parent else null }
    }

    private fun walkClass(
        cls: FlatClass,
        enclosingFunction: String?,
        map: MutableMap<String, String?>,
    ) {
        for (method in cls.methods) {
            map[method.qualifiedName] = enclosingFunction
        }
        for (nested in cls.nestedClasses) walkClass(nested, enclosingFunction, map)
    }

    private fun buildChildrenMap(parentMap: Map<String, String?>): Map<String, List<String>> {
        val out = HashMap<String, MutableList<String>>()
        for ((child, parent) in parentMap) {
            if (parent == null) continue
            out.getOrPut(parent) { ArrayList() }.add(child)
        }
        return out
    }

    private fun collectLocalDefs(fn: FlatFunctionIR): Set<String> {
        val out = HashSet<String>()
        for (block in fn.cfg.blocks) {
            for (inst in block.instructions) {
                inst.targets.forEach { addLocalName(it, out) }
            }
        }
        return out
    }

    private fun addLocalName(value: FlatValue, out: MutableSet<String>) {
        if (value is FlatLocal) out.add(value.name)
    }

    private fun collectLocalReads(fn: FlatFunctionIR): Set<String> {
        val out = HashSet<String>()
        for (block in fn.cfg.blocks) {
            for (inst in block.instructions) {
                for (operand in inst.operands) addLocalName(operand, out)
            }
        }
        return out
    }

    companion object {
        fun analyze(module: FlatModuleIR) = ClosureAnalyzer(module).analyze()
    }
}
