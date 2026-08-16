package org.opentaint.dataflow.jvm.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyFinalFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyInitialFactAp
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.jvm.Action
import org.opentaint.dataflow.configuration.jvm.AssignMark
import org.opentaint.dataflow.configuration.jvm.ClassStatic
import org.opentaint.dataflow.configuration.jvm.ConstantEq
import org.opentaint.dataflow.configuration.jvm.ConstantGt
import org.opentaint.dataflow.configuration.jvm.ConstantLt
import org.opentaint.dataflow.configuration.jvm.ConstantMatches
import org.opentaint.dataflow.configuration.jvm.ContainsMark
import org.opentaint.dataflow.configuration.jvm.CopyAllMarks
import org.opentaint.dataflow.configuration.jvm.CopyMark
import org.opentaint.dataflow.configuration.jvm.IsConstant
import org.opentaint.dataflow.configuration.jvm.IsNull
import org.opentaint.dataflow.configuration.jvm.IsStaticField
import org.opentaint.dataflow.configuration.jvm.JirCondition
import org.opentaint.dataflow.configuration.jvm.Position
import org.opentaint.dataflow.configuration.jvm.PositionWithAccess
import org.opentaint.dataflow.configuration.jvm.RemoveAllMarks
import org.opentaint.dataflow.configuration.jvm.RemoveMark
import org.opentaint.dataflow.configuration.jvm.TaintCleaner
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSource
import org.opentaint.dataflow.configuration.jvm.TaintPassThrough
import org.opentaint.dataflow.configuration.jvm.TypeMatches
import org.opentaint.dataflow.configuration.jvm.TypeMatchesPattern
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLambdaTracker
import org.opentaint.dataflow.jvm.ap.ifds.LambdaAnonymousClassFeature
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ap.ifds.taint.toApAccessor
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.ext.cfg.callExpr
import org.opentaint.ir.api.jvm.ext.findMethodOrNull
import org.opentaint.ir.api.jvm.ext.usedFields
import java.util.ArrayDeque

/**
 * Context-sensitive reachability index for state stored below [ClassStatic].
 *
 * The index is built after prescan, when concrete and lambda call targets are known. A footprint
 * contains every program-static access and every rule position reachable from the method. Missing
 * contexts are represented as unknown and therefore never permit pruning.
 */
internal class JIRClassStaticFootprintIndex(
    private val callResolver: JIRCallResolver,
    private val taintRules: TaintRulesProvider,
    private val contexts: () -> Collection<JIRMethodAnalysisContext>,
) {
    private data class StaticAccessPath(val accessors: List<Accessor>)

    private data class Node(
        val method: MethodWithContext,
        val context: JIRMethodAnalysisContext,
        val directAccesses: Set<StaticAccessPath>,
        val callees: IntArray,
        val hasUnknownCallee: Boolean,
    )

    private data class Index(
        val nodeIds: Map<MethodWithContext, Int>,
        val componentByNode: IntArray,
        val accesses: List<StaticAccessPath>,
        val footprintByComponent: Array<LongArray>,
        val unknownByComponent: BooleanArray,
    )

    @Volatile
    private var index: Index? = null

    fun reset() {
        index = null
    }

    fun mayObserve(method: MethodWithContext, fact: FactAp): Boolean {
        val index = getOrBuildIndex()
        val node = index.nodeIds[method] ?: return true
        val component = index.componentByNode[node]
        if (index.unknownByComponent[component]) return true

        val footprint = index.footprintByComponent[component]
        footprint.forEachSetBit { accessId ->
            if (factMayObserve(fact, index.accesses[accessId])) return true
        }
        return false
    }

    private fun getOrBuildIndex(): Index {
        index?.let { return it }
        return synchronized(this) {
            index ?: buildIndex().also { index = it }
        }
    }

    private fun buildIndex(): Index {
        val contextByMethod = contexts().associateByTo(linkedMapOf()) {
            MethodWithContext(it.methodEntryPoint.method, it.methodEntryPoint.context)
        }
        val methods = contextByMethod.keys.toList()
        val nodeIds = methods.withIndex().associate { (idx, method) -> method to idx }
        val directAccessCache = hashMapOf<JIRMethod, Set<StaticAccessPath>>()

        val nodes = ArrayList<Node>(methods.size)
        for (methodWithContext in methods) {
            val context = contextByMethod.getValue(methodWithContext)
            val method = methodWithContext.method as JIRMethod
            val resolvedCallees = linkedSetOf<MethodWithContext>()
            var hasUnknownCallee = false

            method.instList.forEach { statement ->
                val call = statement.callExpr ?: return@forEach
                callResolver.resolve(call, statement, context).forEach { result ->
                    when (result) {
                        is JIRCallResolver.MethodResolutionResult.ConcreteMethod -> {
                            resolvedCallees += result.method
                        }

                        JIRCallResolver.MethodResolutionResult.MethodResolutionFailed -> {
                            hasUnknownCallee = true
                        }

                        is JIRCallResolver.MethodResolutionResult.Lambda -> {
                            val tracker = context.lambdaCallResolution[statement.location.index]
                                ?: return@forEach
                            tracker.forEachRegisteredLambda(object : JIRLambdaTracker.LambdaSubscriber {
                                override fun newLambda(
                                    method: JIRMethod,
                                    lambdaClass: LambdaAnonymousClassFeature.JIRLambdaClass,
                                ) {
                                    val implementation = lambdaClass.findMethodOrNull(method.name, method.description)
                                    if (implementation == null) {
                                        hasUnknownCallee = true
                                    } else {
                                        resolvedCallees += MethodWithContext(implementation, EmptyMethodContext)
                                    }
                                }
                            })
                        }
                    }
                }
            }

            val calleeIds = IntArray(resolvedCallees.size)
            var calleeCount = 0
            resolvedCallees.forEach { callee ->
                val calleeId = nodeIds[callee]
                if (calleeId == null) {
                    hasUnknownCallee = true
                } else {
                    calleeIds[calleeCount++] = calleeId
                }
            }

            nodes += Node(
                methodWithContext,
                context,
                directAccessCache.getOrPut(method) { directStaticAccesses(method) },
                calleeIds.copyOf(calleeCount),
                hasUnknownCallee,
            )
        }

        val graph = Array(nodes.size) { nodes[it].callees }
        val reverseGraph = reverseGraph(graph)
        val componentByNode = stronglyConnectedComponents(graph, reverseGraph)
        val componentCount = componentByNode.maxOrNull()?.plus(1) ?: 0

        val allAccesses = nodes.asSequence()
            .flatMap { it.directAccesses.asSequence() }
            .distinct()
            .toList()
        val accessIds = allAccesses.withIndex().associate { (idx, access) -> access to idx }
        val words = (allAccesses.size + Long.SIZE_BITS - 1) / Long.SIZE_BITS
        val footprintByComponent = Array(componentCount) { LongArray(words) }
        val unknownByComponent = BooleanArray(componentCount)

        nodes.forEachIndexed { nodeId, node ->
            val component = componentByNode[nodeId]
            node.directAccesses.forEach { access ->
                footprintByComponent[component].set(accessIds.getValue(access))
            }
            unknownByComponent[component] = unknownByComponent[component] || node.hasUnknownCallee
        }

        val componentCallees = Array(componentCount) { hashSetOf<Int>() }
        val componentCallers = Array(componentCount) { hashSetOf<Int>() }
        graph.forEachIndexed { callerNode, callees ->
            val caller = componentByNode[callerNode]
            callees.forEach { calleeNode ->
                val callee = componentByNode[calleeNode]
                if (caller != callee && componentCallees[caller].add(callee)) {
                    componentCallers[callee].add(caller)
                }
            }
        }

        val remainingCallees = IntArray(componentCount) { componentCallees[it].size }
        val worklist = ArrayDeque<Int>()
        remainingCallees.forEachIndexed { component, count ->
            if (count == 0) worklist += component
        }
        while (worklist.isNotEmpty()) {
            val callee = worklist.removeFirst()
            componentCallers[callee].forEach { caller ->
                footprintByComponent[caller].or(footprintByComponent[callee])
                unknownByComponent[caller] = unknownByComponent[caller] || unknownByComponent[callee]
                if (--remainingCallees[caller] == 0) worklist += caller
            }
        }

        check(remainingCallees.all { it == 0 }) { "Class-static footprint condensation graph contains a cycle" }
        return Index(nodeIds, componentByNode, allAccesses, footprintByComponent, unknownByComponent)
    }

    private fun directStaticAccesses(method: JIRMethod): Set<StaticAccessPath> = buildSet {
        val instructions = method.instList.toList()
        val representative = instructions.firstOrNull() ?: return@buildSet

        val fieldUsages = method.usedFields
        (fieldUsages.reads + fieldUsages.writes).asSequence()
            .filter { it.isStatic }
            .forEach { field ->
                val access = MethodFlowFunctionUtils.mkFieldAccess(field, instance = null)
                    as MethodFlowFunctionUtils.StaticRefAccess
                add(StaticAccessPath(listOf(access.classStaticAccessor, access.accessor)))
                taintRules.sourceRulesForStaticField(field, representative, fact = null).forEach { addRule(it) }
            }

        taintRules.entryPointRulesForMethod(method, representative, fact = null).forEach { addRule(it) }
        taintRules.sinkRulesForMethodEntry(method, representative, fact = null).forEach { addRule(it) }
        taintRules.exitSourceRulesForMethod(method, representative, fact = null).forEach { addRule(it) }
        taintRules.sinkRulesForMethodExit(
            method, representative, fact = null, initialFacts = null,
        ).forEach { addRule(it) }

        instructions.forEach { statement ->
            val call = statement.callExpr ?: return@forEach
            addCallRules(call, statement)
        }
    }

    private fun MutableSet<StaticAccessPath>.addCallRules(call: JIRCallExpr, statement: JIRInst) {
        val method = call.method.method
        taintRules.sourceRulesForMethod(method, statement, fact = null).forEach { addRule(it) }
        taintRules.sinkRulesForMethod(method, statement, fact = null).forEach { addRule(it) }
        taintRules.cleanerRulesForMethod(method, statement, fact = null).forEach { addRule(it) }
        taintRules.passTroughRulesForMethod(method, statement, fact = null).forEach { addRule(it) }
    }

    private fun MutableSet<StaticAccessPath>.addRule(rule: TaintConfigurationItem) {
        when (rule) {
            is TaintConfigurationSource -> {
                addCondition(rule.condition)
                rule.actionsAfter.forEach { addAction(it) }
            }

            is TaintConfigurationSink -> {
                addCondition(rule.condition)
                rule.trackFactsReachAnalysisEnd.forEach { addAction(it) }
            }

            is TaintPassThrough -> {
                addCondition(rule.condition)
                rule.actionsAfter.forEach { addAction(it) }
            }

            is TaintCleaner -> {
                addCondition(rule.condition)
                rule.actionsAfter.forEach { addAction(it) }
            }
        }
    }

    private fun MutableSet<StaticAccessPath>.addAction(action: Action) {
        when (action) {
            is AssignMark -> addPosition(action.position)
            is CopyAllMarks -> {
                addPosition(action.from)
                addPosition(action.to)
            }
            is CopyMark -> {
                addPosition(action.from)
                addPosition(action.to)
            }
            is RemoveAllMarks -> addPosition(action.position)
            is RemoveMark -> addPosition(action.position)
        }
    }

    private fun MutableSet<StaticAccessPath>.addCondition(condition: CommonCondition<JirCondition>) {
        when (condition) {
            CommonCondition.True -> Unit
            is CommonCondition.Atom -> condition.atom.positionOrNull()?.let { addPosition(it) }
            is CommonCondition.Not -> addCondition(condition.arg)
            is CommonCondition.And -> condition.args.forEach { addCondition(it) }
            is CommonCondition.Or -> condition.args.forEach { addCondition(it) }
        }
    }

    private fun JirCondition.positionOrNull(): Position? = when (this) {
        is IsConstant -> position
        is IsNull -> position
        is ConstantEq -> position
        is ConstantLt -> position
        is ConstantGt -> position
        is ConstantMatches -> position
        is ContainsMark -> position
        is TypeMatches -> position
        is TypeMatchesPattern -> position
        is IsStaticField -> position
        else -> null
    }

    private fun MutableSet<StaticAccessPath>.addPosition(position: Position) {
        position.staticAccessPath()?.let(::add)
    }

    private fun Position.staticAccessPath(): StaticAccessPath? {
        val result = arrayListOf<Accessor>()
        fun append(position: Position): Boolean = when (position) {
            is ClassStatic -> {
                result += ClassStaticAccessor(position.className)
                true
            }
            is PositionWithAccess -> append(position.base).also { isStatic ->
                if (isStatic) result += position.access.toApAccessor()
            }
            else -> false
        }
        return if (append(this)) StaticAccessPath(result) else null
    }

    private fun factMayObserve(fact: FactAp, access: StaticAccessPath): Boolean {
        var current: FactAp = fact
        access.accessors.forEach { accessor ->
            current = when (current) {
                is BaseOnlyFinalFactAp -> current.readAccessor(accessor)
                is BaseOnlyInitialFactAp -> current.readAccessor(accessor)
                else -> null
            } ?: return false
        }
        return true
    }

    private fun reverseGraph(graph: Array<IntArray>): Array<IntArray> {
        val reverse = Array(graph.size) { arrayListOf<Int>() }
        graph.forEachIndexed { caller, callees ->
            callees.forEach { callee -> reverse[callee] += caller }
        }
        return Array(graph.size) { reverse[it].toIntArray() }
    }

    private fun stronglyConnectedComponents(graph: Array<IntArray>, reverse: Array<IntArray>): IntArray {
        val visited = BooleanArray(graph.size)
        val finishOrder = IntArray(graph.size)
        var finishSize = 0
        val nodeStack = IntArray(graph.size)
        val edgeStack = IntArray(graph.size)

        graph.indices.forEach { root ->
            if (visited[root]) return@forEach
            var depth = 0
            nodeStack[depth] = root
            edgeStack[depth] = 0
            visited[root] = true
            while (depth >= 0) {
                val node = nodeStack[depth]
                val edgeIdx = edgeStack[depth]
                if (edgeIdx < graph[node].size) {
                    val next = graph[node][edgeIdx]
                    edgeStack[depth] = edgeIdx + 1
                    if (!visited[next]) {
                        depth++
                        nodeStack[depth] = next
                        edgeStack[depth] = 0
                        visited[next] = true
                    }
                } else {
                    finishOrder[finishSize++] = node
                    depth--
                }
            }
        }

        val componentByNode = IntArray(graph.size) { -1 }
        var component = 0
        for (orderIdx in finishSize - 1 downTo 0) {
            val root = finishOrder[orderIdx]
            if (componentByNode[root] >= 0) continue
            var size = 1
            nodeStack[0] = root
            componentByNode[root] = component
            while (size > 0) {
                val node = nodeStack[--size]
                reverse[node].forEach { next ->
                    if (componentByNode[next] < 0) {
                        componentByNode[next] = component
                        nodeStack[size++] = next
                    }
                }
            }
            component++
        }
        return componentByNode
    }

    private fun LongArray.set(bit: Int) {
        this[bit / Long.SIZE_BITS] = this[bit / Long.SIZE_BITS] or (1L shl (bit % Long.SIZE_BITS))
    }

    private fun LongArray.or(other: LongArray) {
        indices.forEach { idx -> this[idx] = this[idx] or other[idx] }
    }

    private inline fun LongArray.forEachSetBit(body: (Int) -> Unit) {
        forEachIndexed { wordIdx, wordValue ->
            var word = wordValue
            while (word != 0L) {
                val bit = java.lang.Long.numberOfTrailingZeros(word)
                body(wordIdx * Long.SIZE_BITS + bit)
                word = word and (word - 1)
            }
        }
    }
}
