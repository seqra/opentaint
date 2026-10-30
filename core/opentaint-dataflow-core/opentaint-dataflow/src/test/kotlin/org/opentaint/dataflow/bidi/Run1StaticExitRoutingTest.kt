package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.fixtures.withRun1MarkMode
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import kotlin.test.*

class Run1StaticExitRoutingTest {
    @Test fun `static result enters only the post-return boundary and then uses ordinary exit rules`() {
        MethodAnalysisFixtures().use { f ->
            val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
            val path = listOf(cls, f.field("f"))
            val t = MarkSlot.Concrete(f.mark("T"))
            val original = f.manager.initial(f.pattern(AccessPathBase.Argument(0), tail = Tail.STAR, mark = t))
            val static = f.fact(STATIC, path, Tail.EXACT, t, layer = Layer.DEMAND)
            val ret = f.pattern(AccessPathBase.Return, mark = t)
            val transfer = PathEdge(f.pattern(STATIC, path, Tail.EXACT, t).fact, ret.fact, ExclusionSet.Empty)
            f.exitRules(2, ExitRules(RuleStatement(StatementSummary(setOf(STATIC), listOf(MicroEdge.of(transfer)),
                emptyList(), emptyMap()), StatementSummary.EMPTY, emptyList()), false, emptySet()))
            // A return transfer must never run on the shortcut.
            f.statement(1, StatementSummary(setOf(STATIC), emptyList(), emptyList(), emptyMap()))
            val actor = f.core()
            actor.routeStaticResultToExit(f.inst(1), original, static)
            assertTrue(actor.summaries.all().none(), "Producer cannot insert a summary before exit rules")
            assertTrue(actor.edges.edgesAt(f.inst(1)).any(), "Shortcut output belongs to its producer")
            assertTrue(actor.edges.edgesAt(f.inst(2)).none(), "Exit input is not a completed exit result")
            f.drain(actor)
            assertEquals(setOf(2), f.processed.filter { it.facts.base == STATIC }.map { it.node.location.index }.toSet())
            assertTrue(actor.summaries.all().any { it.first === original && it.second.base == AccessPathBase.Return })
            assertTrue(actor.summaries.all().none { it.second.base == STATIC })
        }
    }

    @Test fun `local producer supply survives a complete exit kill and no relation is archived`() {
        MethodAnalysisFixtures().use { f ->
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val t = f.manager.marks.runtimeAtom(f.mark("T"), MarkMode.GROUP)
            val value = f.fact(STATIC, path, Tail.EXACT, MarkSlot.Concrete(t), layer = Layer.DEMAND)
            f.exitRules(2, ExitRules(RuleStatement(StatementSummary(setOf(STATIC), emptyList(), emptyList(), emptyMap()),
                StatementSummary.EMPTY, emptyList()), false, emptySet()))
            val actor = f.core()
            val operation = OperationId(FormKey(FormOwner(), f.key.method, f.key, f.inst(0)))
            actor.emitOperationResult(OperationInput(ResumeSite.StatementInput(operation), f.manager.zero, Reach.NORMAL),
                StaticOperation.Write(operation, f.ops.leaves(value).single()), value) { _, _ -> fail("No ordinary successor") }
            assertTrue(actor.staticBatch.supplies.any { it.groups == MarkSet.of(t) })
            assertTrue(actor.staticBatch.writes.isNotEmpty())
            assertTrue(actor.summaries.all().none())
            f.drain(actor)
            assertTrue(actor.summaries.all().none())
            assertTrue(actor.staticGuidanceSeeds.frozenRows().none())
            val reply = checkNotNull(actor.runnerPort.staticService).commit(StaticBatch().apply {
                interests += StaticInterest(f.store.key("observer"), 1,
                    f.pattern(STATIC, path, Tail.STAR, MarkSlot.STAR), MarkSet.of(t))
            }).filterIsInstance<StaticOwnerEffect.PointReady>()
            assertEquals(listOf(MarkSet.of(t)), reply.map { it.supply.groups })
        }
    }

    @Test fun `post-exit static source completes one boundary pipeline without rescheduling itself`() {
        MethodAnalysisFixtures().use { f ->
            val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
            val from = listOf(cls, f.field("from")); val to = listOf(cls, f.field("to"))
            val initial = f.manager.initial(f.pattern(STATIC, from, Tail.STAR, MarkSlot.STAR))
            val value = f.fact(STATIC, from, Tail.STAR, MarkSlot.STAR, layer = Layer.DEMAND)
            val transfer = starEdge(STATIC, from, STATIC, to)
            val operation = OperationId(FormKey(FormOwner(), f.key.method, f.key, f.inst(2)))
            val rules = StatementSummary(setOf(STATIC), listOf(MicroEdge.of(transfer)), emptyList(), emptyMap(),
                staticOperations = listOf(StaticOperation.Write(operation, Pattern(transfer.to, ExclusionSet.Empty), transfer)))
            f.exitRules(2, ExitRules(RuleStatement(rules, StatementSummary.EMPTY, emptyList()), false, emptySet()))
            val actor = f.core()
            repeat(3) { actor.routeStaticResultToExit(f.inst(1), initial, value) }
            f.drain(actor)
            assertEquals(1, f.processed.count { it.facts.base == STATIC }, "Equal shortcut arrivals share point admission")
            assertTrue(actor.summaries.all().none(), "Static/static is a private handoff seed")
            assertEquals(1, actor.staticGuidanceSeeds.frozenRows().count())
            assertTrue(f.publications.flatten().isEmpty())
            assertTrue(actor.work(1), "Boundary-generated statics must not loop through NormalExit")
        }
    }

    @Test fun `late boundary mark answer resumes exit rules and captures its colored guide`() {
        MethodAnalysisFixtures().use { f ->
            val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
            val from = listOf(cls, f.field("from")); val target = listOf(cls, f.field("target"))
            val atom = f.manager.marks.runtimeAtom(f.mark("T"), MarkMode.GROUP)
            val rule = object : CommonTaintConfigurationSink {
                override val id = "late normal exit sink"
                override val meta = object : CommonTaintConfigurationSinkMeta {
                    override val message = id
                    override val severity = CommonTaintConfigurationSinkMeta.Severity.Warning
                }
            }
            val sink = SinkRule(rule, 0, listOf(f.pattern(STATIC, target, Tail.EXACT, MarkSlot.Concrete(atom))), emptyList())
            f.exitRules(2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, listOf(sink)), false, emptySet()))
            val actor = f.core(localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            val initial = f.manager.initial(f.pattern(STATIC, from, Tail.STAR, MarkSlot.STAR))
            actor.routeStaticResultToExit(f.inst(1), initial, f.fact(STATIC, target, Tail.STAR, MarkSlot.STAR, layer = Layer.DEMAND))
            f.drain(actor)
            assertTrue(f.vulnerabilities.witnessesOf(1).none())
            val before = f.processed.count { it.facts.base == STATIC }
            val effects = checkNotNull(actor.runnerPort.staticService).commit(StaticBatch().apply {
                supplies += RegionGroups(f.pattern(STATIC, from, Tail.STAR, MarkSlot.STAR), MarkSet.of(atom))
            })
            assertTrue(effects.any { it is StaticOwnerEffect.PointReady && it.owner == actor.key })
            for (effect in effects) if (effect.owner == actor.key) actor.onStaticEffect(effect)
            f.drain(actor)
            assertTrue(f.vulnerabilities.witnessesOf(1).any { it.first.rule == rule })
            assertEquals(before, f.processed.count { it.facts.base == STATIC },
                "The reply finishes BoundaryInput directly and must not schedule the shortcut again")
            assertTrue(actor.staticGuidanceSeeds.frozenRows().count() >= 2, "FLOW and its colored exit relation survive handoff")
            assertTrue(actor.work(1))
        }
    }

    /** Review witness for the producer contract: a called method must expose
     * a real write to an earlier read even if its outgoing static value is killed. */
    @Test fun `called conditional writer exposes its pre-exit value before an exit kill`() {
        for (nested in listOf(false, true)) DriverFixtures().use { f ->
            val p = f.program
            val root = p.method("actual writer input", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val writer = p.method("write then local sink", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val relay = p.method("conditional writer relay", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val input = AccessPathBase.LocalVar(0); val arg = AccessPathBase.Argument(0)
            val read = AccessPathBase.LocalVar(1)
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), p.field("f"))
            val mark = p.mark("T")
            val source = PathEdge(ZERO_FACT, p.pattern(input, mark = MarkSlot.Concrete(mark)).fact, ExclusionSet.Empty)
            p.entry(root, RuleStatement(f.summary(ZERO_KEEP, source), StatementSummary.EMPTY, emptyList()))
            p.call(root, 1, CallPlan(setOf(input, arg, STATIC), listOf(
                CallStage.Edges(CallPoint.BEFORE, CallPoint.BOUND, StageKind.BIND_IN,
                    f.summary(ZERO_KEEP, starEdge(input, emptyList(), arg, emptyList()))),
                CallStage.Edges(CallPoint.BOUND, CallPoint.ADDED, StageKind.SOURCES,
                    f.summary(ZERO_KEEP, keepEdge(arg))),
                CallStage.Callees(CallPoint.ADDED, CallPoint.RETURNED, listOf(if (nested) relay else writer)),
                CallStage.Edges(CallPoint.RETURNED, CallPoint.AFTER, StageKind.BIND_BACK, f.summary(ZERO_KEEP)),
            ), emptyList(), CallPoint.BEFORE, CallPoint.AFTER))
            if (nested) p.call(relay, 1, CallPlan(setOf(arg, STATIC), listOf(
                CallStage.Edges(CallPoint.BEFORE, CallPoint.BOUND, StageKind.BIND_IN,
                    f.summary(ZERO_KEEP, keepEdge(arg))),
                CallStage.Callees(CallPoint.BOUND, CallPoint.RETURNED, listOf(writer)),
                CallStage.Edges(CallPoint.RETURNED, CallPoint.AFTER, StageKind.BIND_BACK, f.summary(ZERO_KEEP)),
            ), emptyList(), CallPoint.BEFORE, CallPoint.AFTER))
            fun operation(index: Int) = OperationId(FormKey(FormOwner(), writer.method, writer, p.inst(writer, index)))
            val store = starEdge(arg, emptyList(), STATIC, path)
            p.statement(writer, 0, f.summary(ZERO_KEEP, store).withStaticOperations(listOf(
                StaticOperation.Write(operation(0), Pattern(store.to, ExclusionSet.Empty), store))))
            val load = starEdge(STATIC, path, read, emptyList())
            p.statement(writer, 1, f.summary(ZERO_KEEP, load).withStaticOperations(listOf(
                StaticOperation.Read(operation(1), load))))
            val sink = SinkRule(f.rule("pre-exit write must be visible"), 0,
                listOf(p.pattern(read, mark = MarkSlot.Concrete(mark))), emptyList())
            p.exit(writer, 2, ExitRules(RuleStatement(StatementSummary(setOf(STATIC), emptyList(), emptyList(), emptyMap()),
                StatementSummary.EMPTY, listOf(sink)), false, emptySet()))
            val result = f.run(p.config(roots = listOf(root)))
            assertEquals(RunStatus.COMPLETE, result.status)
            assertTrue(result.witnessesByKey().any { it.key.rule == sink.rule },
                "Exit cleanup cannot hide the actual value from an earlier local read; nested=$nested")
            assertTrue(result.analyzers.all { actor -> actor.summaries.all().none { it.second.base == STATIC } },
                "Producer binding does not fabricate an outgoing method summary after the exit kill")
            assertTrue(f.processed.filter { it.method == root || it.method == relay }
                .none { it.delta.facts.base == STATIC }, "Producer relay does not create caller CFG work")
        }
    }

    /** Review witness: an exit kill removes the outgoing writer summary, but
     * the earlier write can still produce a returned nonstatic value. */
    @Test fun `a pre-exit static write read return keeps the needed later backward demand`() = preExitReturn(0)
    @Test fun `one returning wrapper retains a killed producer dependency for later demand`() = preExitReturn(1)
    @Test fun `two returning wrappers retain a killed producer dependency for later demand`() = preExitReturn(2)

    @Test fun `write read return without an exit kill is a positive demand control`() = preExitReturn(0, kill = false)
    @Test fun `two wrappers without an exit kill are a positive demand control`() = preExitReturn(2, kill = false)

    @Test fun `FULL pre-exit writer still needs the composed return demand`() = preExitReturn(0, markMode = MarkMode.FULL)
    @Test fun `FULL write read return without an exit kill is a positive control`() = preExitReturn(0, kill = false, markMode = MarkMode.FULL)

    private fun preExitReturn(wrappers: Int, kill: Boolean = true, markMode: MarkMode = MarkMode.GROUP) {
        DriverFixtures().use { f ->
            val p = f.program
            val root = p.method("write-read caller", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val getter = p.method("write-read getter", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val relays = List(wrappers) { index ->
                p.method("write-read wrapper $index", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            }
            val input = AccessPathBase.LocalVar(0); val result = AccessPathBase.LocalVar(1)
            val arg = AccessPathBase.Argument(0); val ret = AccessPathBase.Return
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), p.field("f"))
            val mark = p.mark("T")
            val source = PathEdge(ZERO_FACT, p.pattern(input, mark = MarkSlot.Concrete(mark)).fact, ExclusionSet.Empty)
            p.entry(root, RuleStatement(f.summary(ZERO_KEEP, source), StatementSummary.EMPTY, emptyList()))
            p.call(root, 1, CallPlan(setOf(input, result, arg, ret, STATIC), listOf(
                CallStage.Edges(CallPoint.BEFORE, CallPoint.BOUND, StageKind.BIND_IN,
                    f.summary(ZERO_KEEP, starEdge(input, emptyList(), arg, emptyList()))),
                CallStage.Callees(CallPoint.BOUND, CallPoint.RETURNED, listOf(relays.firstOrNull() ?: getter)),
                CallStage.Edges(CallPoint.RETURNED, CallPoint.AFTER, StageKind.BIND_BACK,
                    f.summary(ZERO_KEEP, starEdge(ret, emptyList(), result, emptyList()))),
            ), emptyList(), CallPoint.BEFORE, CallPoint.AFTER))
            for (index in relays.indices) p.call(relays[index], 1,
                CallPlan(setOf(arg, ret, STATIC), listOf(
                    CallStage.Edges(CallPoint.BEFORE, CallPoint.BOUND, StageKind.BIND_IN,
                        f.summary(ZERO_KEEP, keepEdge(arg))),
                    CallStage.Callees(CallPoint.BOUND, CallPoint.RETURNED,
                        listOf(relays.getOrNull(index + 1) ?: getter)),
                    CallStage.Edges(CallPoint.RETURNED, CallPoint.AFTER, StageKind.BIND_BACK,
                        f.summary(ZERO_KEEP, keepEdge(ret))),
                ), emptyList(), CallPoint.BEFORE, CallPoint.AFTER))
            fun operation(index: Int) = OperationId(FormKey(FormOwner(), getter.method, getter, p.inst(getter, index)))
            val store = starEdge(arg, emptyList(), STATIC, path)
            p.statement(getter, 0, f.summary(ZERO_KEEP, store).withStaticOperations(listOf(
                StaticOperation.Write(operation(0), Pattern(store.to, ExclusionSet.Empty), store))))
            val load = starEdge(STATIC, path, ret, emptyList())
            p.statement(getter, 1, f.summary(ZERO_KEEP, load).withStaticOperations(listOf(StaticOperation.Read(operation(1), load))))
            if (kill) p.exit(getter, 2, ExitRules(RuleStatement(StatementSummary(setOf(STATIC), emptyList(), emptyList(), emptyMap()),
                StatementSummary.EMPTY, emptyList()), false, emptySet()))
            val sink = SinkRule(f.rule("returned pre-exit static value"), 0,
                listOf(p.pattern(result, mark = MarkSlot.Concrete(mark))), emptyList())
            p.exit(root, 2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, listOf(sink)), false, emptySet()))
            val report = withRun1MarkMode(markMode) { f.driver(FixedLimits(listOf(1, 1, 2))) }.analyze(listOf(root))
            assertTrue(f.results.first().witnessesByKey().any { it.key.rule == sink.rule }, "Run-1 must discover this candidate")
            assertTrue(f.results.all { it.status == RunStatus.COMPLETE })
            val trace = buildString {
                append("kill=").append(kill).append(" wrappers=").append(wrappers).append(" runs=").append(f.configs.map { it.index }).append(" end=").append(report.end)
                val backward = f.configs.singleOrNull { it.index == 2 }
                append(" getterGuides=").append(backward?.demand?.near(getter, p.pattern(ret, mark = MarkSlot.Concrete(mark))))
                for (run in f.results) {
                    append(" run-").append(run.runIndex).append(" raw=")
                    append(run.analyzers.flatMap { actor -> actor.summaries.all().flatMap { (original, facts) ->
                        f.ops.leaves(facts).map { "${actor.key}: ${original.members.map { it.toPattern() }} -> $it/${facts.layer}" }
                    }.toList() })
                    append(" hits=").append(run.analyzers.flatMap { it.sourceHits?.entries()?.toList().orEmpty() })
                }
            }
            assertTrue(report.entries.any { it.key.rule == sink.rule },
                "A real p-to-return flow through a pre-exit write must survive restricted refinement: $trace")
        }
    }

    @Test fun `a killed pre-exit static to static copy still needs return demand`() {
        DriverFixtures().use { f ->
            val p = f.program
            val root = p.method("static copy caller", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val getter = p.method("static copy getter", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
            val from = listOf(cls, p.field("g")); val target = listOf(cls, p.field("f"))
            val ret = AccessPathBase.Return; val result = AccessPathBase.LocalVar(0)
            val mark = p.mark("T")
            fun operation(owner: MethodKey, index: Int) = OperationId(FormKey(FormOwner(), owner.method, owner, p.inst(owner, index)))
            val source = PathEdge(ZERO_FACT, p.pattern(STATIC, from, mark = MarkSlot.Concrete(mark)).fact, ExclusionSet.Empty)
            p.entry(root, RuleStatement(f.summary(ZERO_KEEP, source).withStaticOperations(listOf(
                StaticOperation.Write(operation(root, 0), Pattern(source.to, ExclusionSet.Empty), source))),
                StatementSummary.EMPTY, emptyList()))
            p.call(root, 1, CallPlan(setOf(STATIC, ret, result), listOf(
                CallStage.Edges(CallPoint.BEFORE, CallPoint.BOUND, StageKind.BIND_IN,
                    f.summary(ZERO_KEEP, keepEdge(STATIC))),
                CallStage.Callees(CallPoint.BOUND, CallPoint.RETURNED, listOf(getter)),
                CallStage.Edges(CallPoint.RETURNED, CallPoint.AFTER, StageKind.BIND_BACK,
                    f.summary(ZERO_KEEP, keepEdge(STATIC), starEdge(ret, emptyList(), result, emptyList()))),
            ), emptyList(), CallPoint.BEFORE, CallPoint.AFTER))
            val copy = starEdge(STATIC, from, STATIC, target)
            p.statement(getter, 0, f.summary(ZERO_KEEP, copy).withStaticOperations(listOf(
                StaticOperation.Read(operation(getter, 0), copy),
                StaticOperation.Write(operation(getter, 0), Pattern(copy.to, ExclusionSet.Empty), copy))))
            val load = starEdge(STATIC, target, ret, emptyList())
            p.statement(getter, 1, f.summary(ZERO_KEEP, load).withStaticOperations(listOf(StaticOperation.Read(operation(getter, 1), load))))
            p.exit(getter, 2, ExitRules(RuleStatement(StatementSummary(setOf(STATIC), emptyList(), emptyList(), emptyMap()),
                StatementSummary.EMPTY, emptyList()), false, emptySet()))
            val sink = SinkRule(f.rule("returned pre-exit static copy"), 0,
                listOf(p.pattern(result, mark = MarkSlot.Concrete(mark))), emptyList())
            p.exit(root, 2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, listOf(sink)), false, emptySet()))
            val report = withRun1MarkMode(MarkMode.GROUP) { f.driver(FixedLimits(listOf(1, 1, 2))) }.analyze(listOf(root))
            assertTrue(f.results.first().witnessesByKey().any { it.key.rule == sink.rule })
            assertTrue(f.results.all { it.status == RunStatus.COMPLETE })
            assertTrue(report.entries.any { it.key.rule == sink.rule },
                "The internal C.g-to-C.f copy is needed even when its outgoing static summary is killed; " +
                    "runs=${f.configs.map { it.index }} end=${report.end}")
        }
    }

    @Test fun `a genuine ZERO writer returns through wrappers after its static exit value is killed`() {
        for (wrappers in listOf(0, 2)) for (mode in MarkMode.entries) DriverFixtures().use { f ->
            val p = f.program
            val root = p.method("zero writer caller", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val writer = p.method("zero writer getter", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val relays = List(wrappers) { index ->
                p.method("zero writer wrapper $index", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            }
            val ret = AccessPathBase.Return
            val local = AccessPathBase.LocalVar(0)
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), p.field("f"))
            val mark = p.mark("T")
            fun call(callee: MethodKey, output: AccessPathBase) = CallPlan(
                setOf(STATIC, ret, output), listOf(
                    CallStage.Edges(CallPoint.BEFORE, CallPoint.BOUND, StageKind.BIND_IN,
                        f.summary(ZERO_KEEP, keepEdge(STATIC))),
                    CallStage.Callees(CallPoint.BOUND, CallPoint.RETURNED, listOf(callee)),
                    CallStage.Edges(CallPoint.RETURNED, CallPoint.AFTER, StageKind.BIND_BACK,
                        f.summary(ZERO_KEEP, keepEdge(STATIC), starEdge(ret, emptyList(), output, emptyList()))),
                ), emptyList(), CallPoint.BEFORE, CallPoint.AFTER)
            p.call(root, 1, call(relays.firstOrNull() ?: writer, local))
            for (index in relays.indices) p.call(relays[index], 1,
                call(relays.getOrNull(index + 1) ?: writer, ret))
            fun operation(index: Int) = OperationId(FormKey(FormOwner(), writer.method, writer, p.inst(writer, index)))
            val source = PathEdge(ZERO_FACT, p.pattern(STATIC, path,
                mark = MarkSlot.Concrete(mark)).fact, ExclusionSet.Empty)
            p.statement(writer, 0, f.summary(ZERO_KEEP, source).withStaticOperations(listOf(
                StaticOperation.Write(operation(0), Pattern(source.to, ExclusionSet.Empty), source))))
            val read = starEdge(STATIC, path, ret, emptyList())
            p.statement(writer, 1, f.summary(ZERO_KEEP, read).withStaticOperations(listOf(
                StaticOperation.Read(operation(1), read))))
            p.exit(writer, 2, ExitRules(RuleStatement(
                StatementSummary(setOf(STATIC), emptyList(), emptyList(), emptyMap()),
                StatementSummary.EMPTY, emptyList()), false, emptySet()))
            val sink = SinkRule(f.rule("returned zero static source"), 0,
                listOf(p.pattern(local, mark = MarkSlot.Concrete(mark))), emptyList())
            p.exit(root, 2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
                listOf(sink)), false, emptySet()))
            val report = withRun1MarkMode(mode) { f.driver(FixedLimits(listOf(1, 1, 2))) }.analyze(listOf(root))
            assertTrue(f.results.all { it.status == RunStatus.COMPLETE }, "mode=$mode wrappers=$wrappers")
            assertTrue(f.results.first().witnessesByKey().keys.any { it.rule == sink.rule })
            assertTrue(report.entries.any { it.key.rule == sink.rule },
                "A real ZERO source dependency survives killed-static guidance; mode=$mode wrappers=$wrappers")
            assertTrue(f.results.single { it.runIndex == 2 }.analyzers.any { actor ->
                actor.sourceHits?.occurrences()?.any { it.method == writer && it.forward == source } == true
            }, "Run-2 must reach the actual source action")
        }
    }

    @Test fun `an intermediate exit write is observed before its continuation discards the value`() {
        MethodAnalysisFixtures().use { f ->
            val actor = f.core()
            actor.addRootZero()
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val value = f.run1Fact(STATIC, path, Tail.EXACT)
            val operation = OperationId(FormKey(FormOwner(), f.key.method, f.key, f.inst(2)))
            var continuations = 0
            actor.emitOperationResult(OperationInput(ResumeSite.BoundaryInput(operation, atStart = false),
                f.manager.zero, Reach.NORMAL), StaticOperation.Write(operation, f.ops.leaves(value).single()), value) { _, _ ->
                continuations++ // A later exit stage kills this value; it never reaches common emission.
            }
            f.drain(actor)
            assertEquals(1, continuations)
            assertTrue(f.processed.none { it.facts.base == STATIC }, "The boundary write must not reschedule NormalExit")
            assertTrue(actor.summaries.all().none { it.second.base == STATIC })
            val lost = actor.freezeStaticWriteCandidates().lostRows().toList()
            assertTrue(lost.any { it.original.isZero && it.result == f.ops.leaves(value).single() },
                "The intermediate value is a required guidance candidate even without a final exit result")
        }
    }

    @Test fun `static shortcut does not need a reachable normal-return predecessor`() {
        MethodAnalysisFixtures(successors = listOf(listOf(1), listOf(1), emptyList())).use { f ->
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val actor = f.core()
            actor.routeStaticResultToExit(f.inst(1), f.manager.zero, f.run1Fact(STATIC, path))
            f.drain(actor)
            assertEquals(setOf(2), f.processed.map { it.node.location.index }.toSet())
            assertTrue(actor.summaries.all().any { it.first.isZero && it.second.base == STATIC })
        }
    }
}
