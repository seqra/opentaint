package org.opentaint.dataflow.bidi.fixtures

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.Seed
import org.opentaint.dataflow.bidi.ap.ReferenceRequestKind as RequestKind
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.bidi.engine.SinkKey
import org.opentaint.dataflow.bidi.interp.ProofKey
import org.opentaint.ir.api.common.cfg.CommonInst

/** Raw observations retain full caller premises and annotations before bounded union comparison. */
data class ObservedEdge(val method: MethodKey, val premise: Set<Pattern>, val conclusion: Conclusion,
                        val node: CommonInst? = null)
data class ObservedInitial(val method: MethodKey, val initial: Pattern)
data class ObservedLink(val callee: MethodKey, val caller: MethodKey, val premise: Set<Pattern>,
                        val callerLayer: Layer, val call: CommonInst, val linkLayer: Layer, val added: Pattern)
data class ObservedRequest(val method: MethodKey, val premise: Pattern, val kind: RequestKind)
data class ObservedSourceHit(val method: MethodKey, val statement: CommonInst, val forward: PathEdge)
data class ObservedSinkEdge(val premise: Set<Pattern>, val layer: Layer, val facts: Set<Conclusion>,
                            val group: GroupKey? = null)
data class ObservedWitness(val rule: RuleId, val methodKey: MethodKey, val statement: CommonInst,
                           val alternative: Int, val run: Int, val edges: List<ObservedSinkEdge>,
                           val endFacts: Set<PathFact>, val confirmed: Boolean = false, val proof: ProofKey? = null)

/** null sink means anonymous DEMAND; a non-null key means NORMAL. */
data class ObservedTarget(val method: MethodKey, val premise: Set<Pattern>, val sink: SinkKey?) {
    val normal: Boolean get() = sink != null
}

data class RunObservation(
    val processed: Set<ObservedEdge> = emptySet(),
    val initials: Set<ObservedInitial> = emptySet(),
    val rawSummaries: Set<ObservedEdge> = emptySet(),
    val publications: Set<ObservedEdge> = emptySet(),
    val selectedDemand: Set<ObservedEdge> = emptySet(),
    val links: Set<ObservedLink> = emptySet(),
    val requests: Set<ObservedRequest> = emptySet(),
    val sourceHits: Set<ObservedSourceHit> = emptySet(),
    val witnesses: Set<ObservedWitness> = emptySet(),
    val targets: Set<ObservedTarget> = emptySet(),
    val sinkSeeds: Set<Seed> = emptySet(),
) {
    fun rawAt(method: MethodKey, premise: Set<Pattern>): Set<Conclusion> =
        rawSummaries.filter { it.method == method && it.premise == premise }.mapTo(LinkedHashSet()) { it.conclusion }

    /** Compare complete unions, not one production leaf against one expected leaf. */
    fun semantic(universe: BoundedDenotation): SemanticRunObservation = SemanticRunObservation(
        normalizeEdges(processed, universe), initials, normalizeEdges(rawSummaries, universe),
        normalizeEdges(publications, universe), normalizeEdges(selectedDemand, universe),
        normalizeLinks(links, universe), requests, sourceHits, normalizeWitnesses(witnesses, universe), targets)

    fun assertEquivalent(other: RunObservation, universe: BoundedDenotation) {
        val expected = semantic(universe)
        val actual = other.semantic(universe)
        if (expected != actual) {
            val differences = ArrayList<String>()
            fun compare(label: String,a: Any,b: Any) {
                if (a==b) return
                if (a is Map<*,*> && b is Map<*,*>) {
                    for (key in (a.keys+b.keys).distinct().filter { a[it]!=b[it] }.take(4))
                        differences += "$label[$key]: expected=${a[key]} actual=${b[key]}"
                } else if (a is Set<*> && b is Set<*>) {
                    differences += "$label: missing=${(a-b).take(4)} extra=${(b-a).take(4)}"
                } else differences += "$label: expected=$a actual=$b"
            }
            compare("initials",expected.initials,actual.initials)
            compare("processed",expected.processed,actual.processed)
            compare("summaries",expected.rawSummaries,actual.rawSummaries)
            compare("publications",expected.publications,actual.publications)
            compare("demand",expected.selectedDemand,actual.selectedDemand)
            compare("links",expected.links,actual.links)
            compare("requests",expected.requests,actual.requests)
            compare("sources",expected.sourceHits,actual.sourceHits)
            compare("witnesses",expected.witnesses,actual.witnesses)
            compare("targets",expected.targets,actual.targets)
            throw AssertionError("Finite closure mismatch\n${differences.joinToString("\n")}\nexpected=$expected\nactual=$actual")
        }
    }
}

enum class ObservationComponent { REACH, FLOW, NORMAL_EXACT, NORMAL_MUST, DEMAND_EXACT, DEMAND_MUST, DEMAND_TAINT }
sealed interface ObservationCell {
    data object Zero : ObservationCell
    data class Location(val value: TestLocation) : ObservationCell
    data class Relation(val value: TestLocationPair) : ObservationCell
}
data class SemanticEdgeHeader(val method: MethodKey, val premise: Set<Pattern>, val node: CommonInst?,
                              val group: GroupKey, val component: ObservationComponent)
data class SemanticLinkHeader(val callee: MethodKey, val caller: MethodKey, val premise: Set<Pattern>,
                              val callerLayer: Layer, val call: CommonInst, val group: GroupKey,
                              val component: ObservationComponent)
data class SemanticSinkHeader(val premise: Set<Pattern>, val layer: Layer, val group: GroupKey)
data class SemanticWitnessHeader(val rule: RuleId, val methodKey: MethodKey, val statement: CommonInst,
                                 val alternative: Int, val run: Int, val edges: List<SemanticSinkHeader>,
                                 val confirmed: Boolean, val proof: ProofKey? = null)
data class SemanticWitness(val edges: List<Map<ObservationComponent, Set<ObservationCell>>>,
                           val endFacts: Set<PathFact>)
data class SemanticRunObservation(
    val processed: Map<SemanticEdgeHeader, Set<ObservationCell>>,
    val initials: Set<ObservedInitial>,
    val rawSummaries: Map<SemanticEdgeHeader, Set<ObservationCell>>,
    val publications: Map<SemanticEdgeHeader, Set<ObservationCell>>,
    val selectedDemand: Map<SemanticEdgeHeader, Set<ObservationCell>>,
    val links: Map<SemanticLinkHeader, Set<ObservationCell>>,
    val requests: Set<ObservedRequest>,
    val sourceHits: Set<ObservedSourceHit>,
    val witnesses: Map<SemanticWitnessHeader, SemanticWitness>,
    val targets: Set<ObservedTarget> = emptySet(),
    val sinkSeeds: Set<Seed> = emptySet(),
)

private fun Conclusion.observationGroup(): GroupKey {
    val layer = if (demand) Layer.DEMAND else Layer.NORMAL
    return when {
        fact.base == AccessPathBase.Zero -> GroupKey(FactsKind.REACH, layer, fact.base)
        fact.mark is MarkSlot.Star -> GroupKey(FactsKind.FLOW, layer, fact.base, exclusion,
            (fact.mark as MarkSlot.Star).excluded)
        else -> GroupKey(FactsKind.TAINT, layer, fact.base, exclusion, tail = Tail.ANY_TAINT)
    }
}
private fun Conclusion.component(): ObservationComponent = when {
    fact.base == AccessPathBase.Zero -> ObservationComponent.REACH
    fact.mark is MarkSlot.Star -> ObservationComponent.FLOW
    demand && fact.tail == Tail.EXACT -> ObservationComponent.DEMAND_EXACT
    demand && fact.tail == Tail.ANY_TAINT -> ObservationComponent.DEMAND_MUST
    demand -> ObservationComponent.DEMAND_TAINT
    fact.tail == Tail.EXACT -> ObservationComponent.NORMAL_EXACT
    else -> ObservationComponent.NORMAL_MUST
}
private fun cells(premise: Set<Pattern>, c: Conclusion, universe: BoundedDenotation): Set<ObservationCell> = when (c.component()) {
    ObservationComponent.REACH -> setOf(ObservationCell.Zero)
    ObservationComponent.FLOW -> premise.flatMap { universe.pairs(it, c) }.mapTo(HashSet()) { ObservationCell.Relation(it) }
    else -> universe.marked(Pattern(c.fact, c.exclusion)).mapTo(HashSet()) { ObservationCell.Location(it) }
}
private fun normalizeEdges(edges: Set<ObservedEdge>, universe: BoundedDenotation): Map<SemanticEdgeHeader, Set<ObservationCell>> {
    val result = LinkedHashMap<SemanticEdgeHeader, MutableSet<ObservationCell>>()
    for (edge in edges) {
        // MAY is already a union containing exact and descendant MAY members.
        // Compare that canonical union, not an old scalar-oracle residue as a
        // separate EXACT component. Layers and complete originals stay fixed.
        if (edge.conclusion.fact.tail in setOf(Tail.EXACT,Tail.ANY) && edges.any { parent ->
                parent !== edge && parent.method == edge.method && parent.node == edge.node &&
                    parent.premise == edge.premise && parent.conclusion.demand == edge.conclusion.demand &&
                    parent.conclusion.fact.tail == Tail.ANY &&
                    parent.conclusion.fact.base == edge.conclusion.fact.base &&
                    parent.conclusion.fact.mark == edge.conclusion.fact.mark &&
                    edge.conclusion.fact.path.startsWith(parent.conclusion.fact.path)
            }) continue
        // T2/T2' can change E or mx while preserving the whole union. Both annotations constrain cells;
        // only kind/layer/base belong in this edge header. Raw DTOs still retain every annotation.
        val group = edge.conclusion.observationGroup().copy(exclusion = ExclusionSet.Empty, markExclusion = MarkExclusions.EMPTY)
        // FLOW cells already contain both input and output locations. Compare
        // the whole relation family; an aligned child need not remain as a
        // separate literal premise after NORMAL relation subsumption.
        val keyPremise = if (edge.conclusion.fact.mark is MarkSlot.Star) emptySet() else edge.premise
        val header = SemanticEdgeHeader(edge.method, keyPremise, edge.node, group,
            edge.conclusion.component())
        result.getOrPut(header, ::LinkedHashSet).addAll(cells(edge.premise, edge.conclusion, universe))
    }
    return result
}
private fun normalizeLinks(links: Set<ObservedLink>, universe: BoundedDenotation): Map<SemanticLinkHeader, Set<ObservationCell>> {
    val result = LinkedHashMap<SemanticLinkHeader, MutableSet<ObservationCell>>()
    for (link in links) {
        val c = Conclusion(link.added.fact, link.added.exclusion, link.linkLayer == Layer.DEMAND)
        val header = SemanticLinkHeader(link.callee, link.caller, link.premise, link.callerLayer, link.call,
            c.observationGroup().copy(exclusion = ExclusionSet.Empty, markExclusion = MarkExclusions.EMPTY), c.component())
        // An added link is an initial location, not the caller-to-output FLOW relation.
        val values = if (c.fact.base == AccessPathBase.Zero) setOf(ObservationCell.Zero)
            else universe.marked(link.added).mapTo(HashSet()) { ObservationCell.Location(it) }
        result.getOrPut(header, ::LinkedHashSet).addAll(values)
    }
    return result
}
private fun sinkGroup(edge: ObservedSinkEdge): GroupKey {
    edge.group?.let { return it }
    require(edge.facts.isNotEmpty())
    val first = edge.facts.first().observationGroup()
    val must = edge.facts.firstOrNull { it.fact.tail == Tail.ANY_TAINT }
    val group = if (must == null) first else must.observationGroup()
    require(edge.facts.all {
        val own = it.observationGroup()
        own.kind == group.kind && own.layer == group.layer && own.base == group.base &&
            own.markExclusion == group.markExclusion &&
            (own.exclusion == group.exclusion || it.fact.tail == Tail.EXACT)
    }) { "One literal support retains one conclusion group" }
    return group
}
private fun normalizeWitnesses(values: Set<ObservedWitness>, universe: BoundedDenotation): Map<SemanticWitnessHeader, SemanticWitness> {
    val result = LinkedHashMap<SemanticWitnessHeader, SemanticWitness>()
    for (witness in values) {
        val headers = witness.edges.map { SemanticSinkHeader(it.premise, it.layer,
            sinkGroup(it).let { group -> group.copy(exclusion = ExclusionSet.Empty, markExclusion = MarkExclusions.EMPTY,
                // Exact members can physically share either TAINT envelope. Typed
                // fact components below retain EXACT/must/may independently.
                tail = if (group.kind == FactsKind.TAINT) Tail.ANY_TAINT else group.tail,
                // The scalar closure compares source/sink observations. Dedicated
                // class tests check H delivery; it is not a distinct report ID.
                protected = false) }) }
        val header = SemanticWitnessHeader(witness.rule, witness.methodKey, witness.statement, witness.alternative,
            witness.run, headers, witness.confirmed, witness.proof)
        val edges = witness.edges.map { edge ->
            val byKind = LinkedHashMap<ObservationComponent, MutableSet<ObservationCell>>()
            for (c in edge.facts) byKind.getOrPut(c.component(), ::LinkedHashSet).addAll(cells(edge.premise, c, universe))
            byKind.mapValues { (_, v) -> v.toSet() }
        }
        val old = result[header]
        result[header] = if (old == null) SemanticWitness(edges, witness.endFacts) else
            SemanticWitness(old.edges.zip(edges) { a, b -> (a.keys + b.keys).associateWith { a[it].orEmpty() + b[it].orEmpty() } },
                old.endFacts + witness.endFacts)
    }
    return result
}

/** These are the only helpers that decode production AP leaves. The raw oracle never calls them. */
fun observedPremise(pk: PremiseKey): Set<Pattern> = pk.members.mapTo(LinkedHashSet()) { it.toPattern() }
fun observedEdges(ops: ApOps, method: MethodKey, pk: PremiseKey, facts: Facts,
                  node: CommonInst? = null): Set<ObservedEdge> = ops.leaves(facts).map {
    ObservedEdge(method, observedPremise(pk), Conclusion(it.fact, it.exclusion, facts.layer == Layer.DEMAND), node)
}.toSet()
fun observedLink(callee: MethodKey, link: Link): ObservedLink = ObservedLink(callee, link.caller.caller,
    observedPremise(link.caller.premise), link.caller.callerLayer, link.caller.call, link.linkLayer, link.addedFact)
fun observedWitness(ops: ApOps, key: VulnerabilityKey, witness: SinkWitness): ObservedWitness =
    ObservedWitness(key.rule, witness.methodKey, key.statement, witness.alternative, witness.run,
        witness.edges.map { edge -> ObservedSinkEdge(observedPremise(edge.premise), edge.layer,
            ops.leaves(edge.facts).map { Conclusion(it.fact, it.exclusion, edge.facts.layer == Layer.DEMAND) }.toSet(),
            edge.facts.groupKey) }, witness.endFacts.toSet(), witness.confirmed, witness.proof)
