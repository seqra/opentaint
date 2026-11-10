# OWASP recurring demand and Thingsboard TenantId writes

10 November 2026. Runtime: `14d7b63369d94f49d4c551be8405ed7719f267cc`;
repository HEAD: `54fdd2b5e`, with the same production code.
This investigation changes no analyzer rule, transfer or stop condition.

OWASP reaches and completes **run-11**, with an accepted forward report from
**run-11**. Thingsboard evidence comes from its existing **run-1 OOM** heap;
it has no completed or accepted iteration. No new Thingsboard scan was run.

The findings are:

1. OWASP produces new nonempty demand on each pass. Later boundary families
   repeat, but the engine has no rule that settles those obligations. DEMAND
   witnesses still create anonymous Targets for already confirmed sinks.
   Shallow FLOW/MUST reversal also recreates DATA demand.
2. Neither TenantId static reference has a Java assignment outside class
   initialization. The large request population must not be described as a
   large number of actual writes to those references. Alias write descriptors,
   admitted FLOW writers, concrete taint supplies and pending readers are
   different populations.

## 1. OWASP: why NO_DEMAND_EDGE is not reached

The stop test in `IterationDriver.barrier` is:

```text
handoff = build demand from current outgoing DEMAND summaries and Targets
if forward && handoff.demandEdges.isEmpty(): stop(NO_DEMAND_EDGE)
else if forward && policy stops this run: stop(RUN_LIMIT)
else: continue with the reversed handoff
```

It does not compare demand with the preceding iteration. It does not stop
when reports stop growing. At run-11 the outgoing handoff remains nonempty,
so the selected hard limit stops the analysis.

The performance report's forward rows are:

| Completed run | Handoff patterns | Raw Target demand | Confirmed findings |
| --- | ---: | ---: | ---: |
| run-5 | 947 | 898 | 2,633 |
| run-7 | 975 | 923 | 2,633 |
| run-9 | 975 | 923 | 2,633 |
| run-11 | 975 | 923 | 2,633 |

These counters alone do not prove that the edges repeat. Raw Target demand
and normalized handoff patterns also have different counting rules.

### Complete boundary and witness capture

An external Java agent recorded joined handoffs and completed forward sink
witnesses. It did not inject seeds, call a transfer or change a store. The
diagnostic run kept FULL mode, aliases/statics, `1,1,2,...`, 8g and the 1000 s
budget. Its final output has all **2,633 exact finding locations unchanged**.
The observer recorded 147,266 rows with zero serialization errors.

The first attempt completed run-11 but its transformer rejected stack frames
and produced no semantic records. The corrected transformer uses expanded
frames and was checked against both target classes before the second run.
Only the second run supplies the semantic comparisons below.

The no-op first attempt reproduces the performance report's 975/923 late
counts. The corrected observed execution has 1017/947. Do not replace the
performance measurements with diagnostic timings or claim that its exact
partition is the original 975 rows. The count variation was not isolated.
The production source is identical, and all exported findings match.

| Completed diagnostic run | DATA rows | Control rows | Total handoff | Outgoing Target rows | Source/sink seeds for the next run |
| --- | ---: | ---: | ---: | ---: | ---: |
| run-5 FORWARD | 69 | 898 | 967 | 912 | 469 sink seeds |
| run-6 BACKWARD | 89 | 1,948 | 2,037 | 430 | 4,423 source permissions |
| run-7 FORWARD | 97 | 920 | 1,017 | 947 | 469 sink seeds |
| run-8 BACKWARD | 117 | 2,011 | 2,128 | 430 | 4,423 source permissions |
| run-9 FORWARD | 97 | 920 | 1,017 | 947 | 469 sink seeds |
| run-10 BACKWARD | 117 | 2,011 | 2,128 | 430 | 4,423 source permissions |
| run-11 FORWARD | 97 | 920 | 1,017 | 947 | 469 sink seeds |

Run-11 builds this handoff before the stop decision. Its prepared seeds do
not imply that run-12 executes.

The comparison expands trie geometry and removes allocation IDs. It keeps
native accessor/mark IDs and labels, tails, exclusions, layers, protection,
method/context strings, block scopes and recorded ports. Equal short labels
for different accessors do not merge. The complete captured families show:

- run-7 and run-9 have identical DATA, controls, outgoing Targets and seeds.
- run-9 and run-11 also have identical current summary packets: 645 in each.
- run-8 and run-10 have identical DATA, controls, outgoing Targets, seeds and
  current summary packets: 1,650 in each.

This is repeated boundary demand, rather than an inference from equal totals.
It is not a proof of equal entire engine states or unlimited non-termination.
For example, 18 unique intermediate witness packets disappear and 18 appear
between run-9 and run-11, although their outgoing families are identical.

### Target feedback: already confirmed sinks still issue demand

In every observed forward run from run-5, **230 physical sink identities**
have DEMAND witnesses. All 230 IDs are already in the accepted confirmed set.
There is no unconfirmed DEMAND-witness ID in these runs.

The witness path uses the layer of the triggering facts:

```text
NORMAL witness -> P -> NormalTarget(reportId)
DEMAND witness -> capture sink seed; P -> DemandTarget
```

The DEMAND arm does not consult the accepted root report IDs. DemandTarget
has no report ID. Suppression of a repeated `P -> NormalTarget(id)` therefore
cannot suppress this anonymous Target. Caller and block propagation create
many Target rows from one physical sink.

The forward run-9/run-11 control rows are exactly:

```text
430: (entry = Target, exit = ZERO)
490: (entry = Target, exit = DATA)
```

The backward run-8/run-10 rows are:

```text
 430: (entry = Target, exit = ZERO)
 430: (entry = ZERO,   exit = ZERO)
1151: (entry = DATA,   exit = ZERO)
```

Thus ZERO routing, source permissions and sink replay remain active even
when the confirmed finding set does not change. These rows are guidance,
not 947 distinct new vulnerabilities.

A concrete captured witness is `BenchmarkTest01000#doPost`, at
`rs = statement.executeQuery()`:

```text
rule:    java/security/sqli.yaml:sql-injection
report:  1708, already accepted
premise: var(27).<string-bytes>.[].$/Tsource
fact:    this.$/Tgenerated, DEMAND
result:  premise -> DemandTarget; capture SQL sink guidance
```

Here `Tsource` is the SQL `$UNTRUSTED` source mark, and `Tgenerated` is that
rule's generated mark `$<ARTIFICIAL>_29`. The packet has an exact leaf, even
though its enclosing packet's tail header is ANY_TAINT. The edge remains
DEMAND. Exact leaf geometry does not make its witness NORMAL.

The raw data includes the complete mark names, scope and fact tree for this
witness, and every other captured witness. This example is not a claim that
every Target uses this same source or generated mark.

### DATA feedback: reverse MUST/FLOW introduces persistent uncertainty

There are DATA obligations as well as Target controls. Deleting Target rows
alone would not make the current no-demand test true.

One principal method is the nested helper in `BenchmarkTest01000`:

```java
String doSomething(HttpServletRequest request, String param) {
    String bar = "";
    if (param != null) {
        bar = new String(Base64.decodeBase64(
                Base64.encodeBase64(param.getBytes())));
    }
    return bar;
}
```

Use `bytes` below for the model field `String#<string-bytes>`; `[]` is the
element accessor, not STAR. All shown marks are FLOW and exclusions are empty.
The capture contains these native relations and handoffs:

```text
run-9 FORWARD, limit8:
  NORMAL param.bytes.[].[any-taint] -> ret.bytes.[any-taint]
  NORMAL param.bytes.[].*          -> ret.*
  DEMAND param.bytes.[].*          -> ret.bytes.[any]

handoff to run-10 includes:
  demand entry ret.bytes.[any], exit param.bytes.[].*

native backward read of the first NORMAL record:
  ret.bytes.* -> param.bytes.[].[any], DEMAND

run-10 BACKWARD, limit9, current output includes:
  DEMAND ret.bytes.* -> param.bytes.[].[any]

handoff to run-11 includes:
  demand entry param.bytes.[].[any], exit ret.bytes.*

run-11 FORWARD, limit10:
  the shown forward relation family is produced again
```

`Reference.kt.mustRecordReadView` explicitly gives the NORMAL FLOW/MUST
record an ANY/DEMAND reverse view. This uncertainty is not a field-limit cut.
The byte-array path has two counted fields, well below limits 8–10. Other
String model fields produce parallel rows; the complete packet lists them.

Short NORMAL STAR summaries coexist with these rows. Their presence does
not currently discharge all different-tail/correlation obligations. The
current selected replacement rules do not turn this handoff into an empty
set. This is a demand-lifetime/native-reversal issue, not evidence that the
analysis needs a larger field limit.

### What this establishes

The current no-demand test behaves as implemented. The design gap is that
the repeated obligations have no proved “answered” state. Sink identity is
lost when the DEMAND Target is built, and native reverse-MUST uncertainty
can survive every larger field limit.

A repair must define which obligations still support an unresolved finding,
and how saved NORMAL providers can discharge intrinsic uncertainty. Do not
stop merely on equal counts or delete every Target whose sink was once seen.
Source permissions and shared dependencies can still serve another sink.
The capture identifies a repair target; it does not select a new stop policy.

## 2. Thingsboard: what really writes the TenantId fields

### Source and bytecode agree on the physical writes

The prepared input contains:

```java
public final class TenantId extends UUIDBased {
    static final ConcurrentReferenceHashMap<UUID,TenantId> tenants =
            new ConcurrentReferenceHashMap<>(16, ReferenceType.SOFT);
    public static final TenantId SYS_TENANT_ID =
            TenantId.fromUUID(EntityId.NULL_UUID);

    public static TenantId fromUUID(UUID id) {
        return tenants.computeIfAbsent(id, TenantId::new);
    }
    public TenantId(UUID id) { super(id); }
}
```

A scan of all **6,196 prepared project-module class files** finds:

| Target | Instruction | Method | Source line |
| --- | --- | --- | ---: |
| `TenantId.tenants` | PUTSTATIC | `TenantId.<clinit>` | 32 |
| `TenantId.SYS_TENANT_ID` | PUTSTATIC | `TenantId.<clinit>` | 35 |
| `UUIDBased.id` | PUTFIELD | `UUIDBased.<init>(UUID)` | 39 |
| `UUIDBased.hash` | PUTFIELD | `UUIDBased.hashCode()` | 52 |

There is no other direct assignment to either static reference in those
classes. The scan does not cover reflective, Unsafe, native or external
extension writes.

`tenants` is a mutable cache: `computeIfAbsent` can add a mapping. Final fixes
the map reference, not its contents. `SYS_TENANT_ID` is different: its logical
UUID is final and has no setter. It is an immutable identity in ordinary
application use. Its base class does have a mutable cached hash field, so it
is not accurate to say every Java field is immutable.

### The heap distinguishes descriptors from admitted writers

The new complete query uses the same run-1 OOM snapshot as the performance
report. It does not rerun Thingsboard or infer its completed fixed point.

| Population in the snapshot | tenants | SYS_TENANT_ID |
| --- | ---: | ---: |
| Direct reference write sites in project bytecode | 1 | 1 |
| Reached alias write-operation descriptors | 339 | 405 |
| Source method signatures containing those descriptors | 109 | 177 |
| Source instruction objects in those descriptors | 149 | 269 |
| Registered global FLOW writer rows | 251 | **0** |
| Local writer rows | 323 | **0** |
| Requested but not supplied marks (`req`) | 201 | 219 |
| Supplied but not requested marks (`reach`) | 0 | 0 |
| Requested and supplied marks (`processed`) | 20 | 2 |

All 744 captured write descriptors come from the call-alias form: no action
ID, a call stage ordinal 6–8, and a contextual call FormKey. This is the
`JIRCallPlanBuilder.aliases(back)` path. They are not 744 PUTSTATICs.
On ZERO, `Run1PointResume.reached` retains these descriptors; its Write arm
does not itself register a writer. Registration requires an applied FLOW
effect. The snapshot has no such retained local/global writer for SYS.

The three-set names describe state at capture time. A processed mark is not
an unrequested reach mark. Pending owner replies can still be queued when
the OOM occurs. Do not treat this interrupted snapshot as proof that no other
mark could ever arrive.

### Principal cache pattern: a call result aliases a cached TenantId

In `DefaultTbClusterService#pushMsgToRuleEngine`:

```java
if (tenantId == null || tenantId.isNullUid()) {
    if (entityId.getEntityType().equals(EntityType.TENANT)) {
        tenantId = TenantId.fromUUID(entityId.getId());
    } else { return; }
} else {
    // profile lookup and message transformation
}
ruleEngineProducerService.sendToRuleEngine(
        producerProvider.getRuleEngineMsgProducer(), tenantId, tbMsg, callback);
// Source line258; captured instruction26.
```

At that send call the native alias form contains both:

```text
arg(1).* -> S.TenantId.tenants.MapValue.* / FLOW
arg(2).* -> S.TenantId.tenants.MapValue.* / FLOW
```

These are call bind-back micro-edges to a persisted alias. They do not mean
the Java statement reassigns the `tenants` reference. The MapValue slot is
the map model's value location. The second edge also shows that the modeled
alias relation can mix the message with the cached value; the full derivation
of that DSU equivalence was not captured by this query.

At run-1's field budget, the MapValue suffix is cut. The retained writer
output is:

```text
P -> S.TenantId.tenants.[any] / FLOW, DEMAND
```

250 of the global rows are in this source method, under **36 method keys**;
one more is in `LwM2MClientSerDes#deserialize`, at similar call-alias points.
The local directory has 322 rows for the first method and one for the second.
For the first method there are seven distinct original patterns and two
output patterns, with different FLOW mark exclusions, repeated across those
contexts. Rows are not distinct source write statements. Local and committed
global rows are separate populations at this interrupted batching point.

### Principal SYS pattern: passing the constant through a call

`AbstractCleanUpService#isSystemTenantPartitionMine` only reads the constant:

```java
return partitionService.resolve(ServiceType.TB_CORE,
        TenantId.SYS_TENANT_ID, TenantId.SYS_TENANT_ID).isMyPartition();
```

The call alias form contains:

```text
arg(1).* -> S.TenantId.SYS_TENANT_ID.* / FLOW
arg(2).* -> S.TenantId.SYS_TENANT_ID.* / FLOW
```

This returns potential effects on the pointed-to object through its alias.
It is not an assignment to the final reference. The MemoryEffect guard and
actual input/application decide whether it produces an effect; retaining
the descriptor alone does not prove a write.

375 SYS descriptors target the constant root. The remaining 30 have suffixes,
including `UUIDBased.id`, `AliasEntityIdImpl.entityType`, `IdBased.id` and
repeated `HttpHeaders.headerValues`. These are modeled alias paths, not
evidence that the final TenantId object physically has those Java fields.
They identify an alias-precision question worth a separate producer trace.

### Why immutability does not imply “cannot have a mark”

The SYS pool already has two supplied-and-requested FULL marks: an XSS Spring
source mark and a path-traversal Spring source mark. A taint label can arrive
through a source rule or modeled alias without a Java field assignment.
The snapshot does not retain the full producer history of those two supplies.

For example, a configured source action can assign T to the argument in
`markSource(TenantId.SYS_TENANT_ID)` without changing any Java field. Removing
all final-reference taint effects would change that rule's meaning.

Therefore, a safe future change must distinguish physical object mutation,
taint assignment and approximate call aliases. Final alone is not a valid
reason to delete all taint propagation. There is no such filter in this work.

### Relation to the OOM

The earlier complete census has 1,396,027 pending memberships from `tenants`
and 1,217,455 from SYS: **2,613,482 combined, 92.425% of all pending marks**.
The new query shows why this must not be called a writer-count explosion:
the service has only 251 registered rows for the two fields, all for tenants.
There is a large reader/continuation × mark population, including 219 SYS
marks still awaiting supply, despite a tiny physical write set.

The concrete next questions are: can field-specific producer availability
avoid these speculative continuations, and which call-alias paths represent
real object effects rather than a taint-copy approximation? Those need a
separate design and proof. The current data does not justify silently dropping
the constant, weakening source actions or changing alias semantics.

## Evidence and checks

The [data record](data/bidirectional-owasp-demand-tenant-writes-20261110.json)
embeds counters, comparisons, bytecode writes, source hashes/text, observer
and decoder source, and command receipts. It links complete compressed rows:

- [OWASP native records](data/bidirectional-owasp-recurring-demand-native-20261110.jsonl.gz).
- [OWASP canonical comparison records](data/bidirectional-owasp-recurring-demand-canonical-20261110.jsonl.gz).
- [Thingsboard writer/operation records](data/bidirectional-tenant-static-writes-native-20261110.jsonl.gz).

The heap reader first rejected a previously unhandled IntArray list view.
That attempt has no accepted result. Its corrected decoder preserves every
integer accessor and checks the view's structure. The final query is complete;
the MAT process exit alone was not used as proof of query success.
Original heap size and modification time are unchanged. All analyzer and
query processes are terminal. Production source remains unchanged.
