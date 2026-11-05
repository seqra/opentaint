# Stirling run-8: remaining field-path work after canonicalization

This is a **bounded diagnostic**, on runtime `8331bf9e326ddd1bd5083dbc50456963d6b26b52`. It explains actual remaining operations; it does not identify the cause of the two missing Conductor findings or measure their CPU cost. The [portable evidence](data/bidirectional-stirling-canonical-field-trace-20261105.json) contains complete selected events, DAGs, marks, masks, premises, source excerpts and hashes.

The main Stirling command timed out at **run-16 reached / run-15 completed / run-15 accepted**. The separate trace replay was deliberately stopped after its first **4,096 event attempts**, with **run-8 reached / run-7 completed / run-7 accepted**. Its analyzer process is dead. Run-8 did not complete in this diagnostic; these are not new performance or quality measurements.

## Code and capture boundary

The exact owner is:

```text
EmlProcessingUtils#decodeMimeHeader(String)
context: arg(0) == java.lang.StringBuilder
run 8, BACKWARD, field limit 7
```

The Java method, lines 492–557 of the pinned project source, builds a `StringBuilder`, loops on `matcher.find()`, reads `matcher.group(1/2/3)`, decodes B/Q values, appends decoded or original groups, and returns `result.toString()`. The native trace contains the library-model fields `Matcher#group`, `Matcher#pattern`, `Pattern#regex`, `String#bytes`, and synthetic rule-storage fields. Its register numbers are preserved below; this capture does not supply a full register-to-Java-variable map. The StringBuilder context and mixed field names alone do not establish an alias/type defect.

Notation: `RS` is `CharSequence#<rule-storage>`. `[element]` is the captured accessor 11, whose name `*` is `ElementAccessor`; it is **not** a `STAR` tail. `FLOW\{75,76}` excludes the two named full crypto marks in the embedded catalog. Those are exclusions, not the two taints being propagated. All omitted `E` sets are empty. `P` has no layer; `N` and `D` annotate actual/output facts.

All 4,096 events decoded without errors, omitted events or partial scalar expansion. Every captured premise is singleton; every captured fact stream has one leaf. This prefix contains FLOW packets only, with no concrete TAINT/protection packet. The controller saw no source drop record. It stopped before a source final-statistics footer could be emitted.

| Stage | Events in this prefix |
|---|---:|
| Local input offers | 32 |
| Local direct/current relation callbacks | 522 |
| Explicit opposite-record applications | 283 |
| Applied / kept / completion | 792 each |
| Full loop observations | 456 |
| C5 normalized candidates / admitted rows | 407 / 20 |

The direct-relation event does not distinguish CURRENT from SAVED_DIRECT. The opposite-record event is explicit. C5 counts are event counts, not a one-to-one rejection ratio: intersections can emit multiple rows, and the normalized hook precedes other native gates.

## A real writer survives the new relation antichain

Offer **3293** supplies the same exact local interface throughout this example:

```text
parent: root block 0, entry ROOT_ENTRY(-1)
child:  loop block 2, entry port 80
exit:   port 20; completion point 20
P:      ret.String#bytes.STAR/FLOW
actual: var(21).String#bytes.STAR/FLOW N
```

Two native relation callbacks then occur:

```text
3314: I = var(21).STAR/FLOW
      O = var(23).STAR/FLOW
      applied = var(23).String#bytes.STAR/FLOW N

3318: I = var(21).STAR/FLOW
      O = var(23).[element].STAR/FLOW
3319: applied = var(23).[element].String#bytes.STAR/FLOW N
```

Both relations are NORMAL: native application cannot erase a DEMAND incoming/relation layer to produce this NORMAL output. The shorter output does **not** subsume the writer under the selected correlated law. The input residual is empty, while the second output adds `[element]`. The law requires the *same residual* on both sides; it does not authorize deleting every longer output under a fixed input.

Events **3320** and **3321** observe the full and cut output. Both have the same complete support: no adjacent admission; a repeat NORMAL admission `var(23).[element].STAR/FLOW`; and four enclosing DEMAND results under the original `P`:

```text
arg(0).[element].ANY/FLOW
arg(0).Matcher#group.ANY/FLOW
arg(0).Matcher#<rule-storage>.ANY/FLOW
arg(0).ANY/FLOW
```

The gate therefore keeps `var(23).[element].ANY/FLOW D` at **3322**, and completion **3323** is fresh. This is a visible NORMAL-to-DEMAND prefix cut after a field-growing summary application.

At **4007–4008**, root C5 separately admits the exact same original `P` with `arg(0).String#bytes.STAR/FLOW N`. This is an actual endpoint result, not a claim that it uniquely descended from cut 3322: queued callbacks and several alternative relations coexist.

There are **55** observed compatible pure NORMAL STAR relation geometries at exact child scope and exit, and **zero** strict aligned shorter/longer cover candidates among those geometries. This is a prefix inventory of executed NORMAL outcomes, not an exhaustive inventory of all stored rows. It supports the narrower conclusion that the displayed remaining writer is outside the selected antichain law.

## Coarse MAY input still activates deep MAY rows

The first offer is `ret.ANY/FLOW D`, with original `P = ret.ANY/FLOW`. Later, AL scope `(block 3, ROOT_EXIT)` produces:

```text
2702, normalized:
    ret.RS.RS.RS.RS.ANY/FLOW
      -> var(21).RS.RS.RS.ANY/FLOW\{75,76} D

2703, admitted by C5:
    ret.RS.RS.RS.RS.ANY/FLOW
      -> var(21).RS.RS.RS.File#uri.ANY/FLOW\{75,76} D
```

C5 selects a deeper demanded field inside the MAY region. Its complete demand-pair identities/budgets are not in this trace, so the event is evidence of the resulting intersection, not a reconstructed pair.

The exact admitted I/O pair appears in relation **2796**. Its enclosing original remains `ret.ANY/FLOW`; the coarse standing MAY offer can match that deeper MAY premise. Application **2797** produces the depth-four `var(21).RS.RS.RS.File#uri.ANY/FLOW\{75,76} D`; **2798** keeps it, and **2799** has no fresh completion. An identical persisted row might also exist: matching produced/applied keys do not establish unique publication history.

These are DEMAND/MAY relations across different premises. They are outside the NORMAL STAR relation index. The selected directional change also retains incoming MAY ancestor matching; it narrows incoming **STAR** ancestry. Consequently, neither selected rule removes this example. This is a concrete source of remaining deep approximate fields, without an unsupported claim that the synthetic field chain is a feasible Java heap path.

## Deduplication works after repeated work

Completions are fresh **92/792 (11.62%)**; the other 700 produce no delta. There are **542 repeated events with an earlier identical full route and packet key**, all not fresh. The key includes method/run, parent scope, child scope including ingress, actual exit, completion point, complete semantic `P`, and all packet geometry/layer/E/mx/protection. It is stronger than output equality.

For example, **146** is fresh and **336** repeats the exact same key:

```text
parent root(-1), child loop2(entry80), exit20, completion20
P = ret.ANY/FLOW
F = var(23).Matcher#group.ANY/FLOW\{75,76} D
```

Native completion storage is actually keyed by parent owner and `(child block, completion point)`, then complete premise/fact group. The audit additionally requires equal child ingress and actual exit, so it does not inflate the exact-repeat count by merging interfaces. The remaining **158** unsuccessful events are not classified as identical earlier keys; native subsumption and interface merging can also remove work.

Another full chain (**1463, 1492–1497**) offers `var(23).Matcher#group.ANY/FLOW\{75,76} D`, applies `var(23).STAR/FLOW -> var(23).[element].STAR/FLOW`, observes and cuts `[element].Matcher#group.ANY` to `[element].ANY`, then finds no fresh completion. Source control flow confirms that this unsuccessful attempt enqueues no onward route/C5 callback. Its application and observation have already run before deduplication.

Across this prefix, 64 applied facts change at restriction: 25 NORMAL-to-DEMAND cuts and 39 DEMAND-to-DEMAND cuts. Applied/kept depths reach four; C5-normalized candidates reach six. All **456** observation events have repeat **and enclosing** support, with no adjacent initials. This is not a repeat-only justification. There are 167 distinct exact observation input keys and 289 repeated query events, but quantum boundaries are unlogged; that is not a bounded-memo hit rate or a saving estimate.

### Pre-gate exact membership in existing restricted output

Post-restriction equality alone overstates a possible early exact-membership check. Among those 542 repeats:

| More restrictive condition | Events |
|---|---:|
| Raw pre-gate packet already equals the kept packet | 505 |
| Raw equals an earlier **fresh** completion at the same full route | 163 |
| Same earlier fresh witness **and still exact-current** | 88 |
| Of those 88, already nongrowing bypasses | 43 |
| Of those 88, growing-loop evaluations | **45** |

The current-membership classification is a **finite source replay**, not a direct historical native-store dump. It retains exact layer, tail, field E, mx, coordinate and native owner. Its observed domain is single-leaf FLOW: MAY with empty E; STAR with empty E or `{String#<string-bytes>}`; no MUST/concrete protection. Replaying all 792 completion offers reproduces every native fresh flag and all 92 full fresh deltas with **zero mismatches**. The model source, checks and complete qualifying keys are embedded in the JSON; this is not a generic Kotlin-equivalence proof.

The 75 historical fresh witnesses absent from the 88 must not be counted as still stored. For example, **146** admits `var(23).Matcher#group.ANY/FLOW\{75,76} D`; broader root-MAY completion **155** removes that exact descendant coordinate. At pre-gate **334**, the descendant is spatially covered but no longer an exact current member. A set of past fresh packets would give the wrong answer.

A qualifying example is fresh completion **3359**, then raw pre-gate **3527**, observation **3528**, unchanged keep **3529**, and nonfresh completion **3530**:

```text
parent root(entry-1), child loop2(entry80), exit80, completion80
P = ret.String#bytes.STAR/FLOW
F = var(23).Matcher#group.String#bytes.STAR/FLOW\{75,76} N
E = {}; protection = none
```

Here both the earlier producer and the new producer are growing-loop rows, and the exact restricted output is still present before the later gate. All 45 qualifying growing evaluations have this prior-gated property and execute one observation each in the captured prefix. Thus **45 of the 456 captured observations** are evidenced candidates for this narrow early check, subject to a preservation argument; not 542. Actual application, requests/Targets, ND effects and route semantics must still run as required. “C5 avoided” would mean the observer's pure enclosing intersection, not the publication C5 that already preceded this application.

The repeated relation pair also explains a present domain limit. Row **3355** has `I=var21.STAR/FLOW`, `O=var23.Matcher#group.STAR/FLOW`, output E `{String#<string-bytes>(204)}`. Row **3526** has `I=var21.String#bytes(1480).STAR/FLOW`, `O=var23.Matcher#group.String#bytes.STAR/FLOW`, empty E. Both outputs have mx `{75,76}` and apply NORMAL to this same input suffix. The covering candidate's E is nonempty, so it is outside the implemented Eempty NORMAL relation law. The excluded accessor 204 is distinct from the actual suffix accessor 1480. No E-aware relation extension is selected here.

Native completion ownership merges child ingress at the same parent/child-block/completion point. If that native identity alone is used, the finite replay finds 139 exact-current raw packets among the 542 repeats (149 among all 792). Fifty-one of those 139 lack the stricter same-ingress earlier fresh witness, and ten more occur outside the 542 strict-route repeats. They are reported separately, not silently promoted into the conservative 45-case result.

## What this establishes

The model source supplies distinct geometric alternatives. [StringBuilder.append(String)](../../model/java/config/stdlib/java-lang-stringbuilder.yaml#L2191) and the [three-argument append](../../model/java/config/stdlib/java-lang-stringbuilder.yaml#L2396) contain all of:

```text
arg(0) -> this                 arg(0) -> this.RS
this   -> result              this.RS -> result
```

They also copy the argument to the result and its rule-storage field. [Matcher.group](../../model/java/config/stdlib/java-util-regex.yaml#L718) has both group-field and `pattern.regex` read paths, in addition to a [root-copy model](../../model/java/config/stdlib/java-util-regex.yaml#L219). The [byte-array String constructor](../../model/java/config/stdlib/java-lang.yaml#L798) writes `this.String#bytes`. These are source-backed read/write shapes consistent with the captured storage/bytes families. They explain why model-created alternatives can have different output offsets, which the correlated antichain must retain. The trace does not identify the unique lowered action and alias composition of every row. Textual duplicates in a model are also not proof of repeated runtime work; lowering can deduplicate identical actions.

There is a separate legacy-policy difference: [TaintAnalyzer.unrollStrategy](../../core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint/common/sast/dataflow/TaintAnalyzer.kt#L72) excludes `<rule-storage>` from ANY unrolling, while [bidi `isCounted`](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/AccessorTable.kt#L58) counts every field and the element accessor. The latter file is byte-identical in `52f32dd` and `8331bf9e`. Rule-storage fields therefore **consume** the current limit; they are neither zero-cost nor unbounded within one fixed limit. This audit selects no model, alias, or budget change.

The remaining pattern combines distinct field-offset relations, deep MAY rows selected by demand, repeated application/observation, and successful final completion deduplication. It is not evidence that identical facts propagate past the completion store, or that the NORMAL relation implementation missed the displayed subsumption.

The MAY-progress discovery probe also completed all **12** genuine source/read-write/branch cases with their expected sink, through run-7 for the deepest case. It did not reproduce Conductor's loss. No concrete protected mark occurs in this Stirling prefix, and no source-permission or whole-project finding-preservation conclusion follows from it. The Conductor first-loss investigation remains separate.
