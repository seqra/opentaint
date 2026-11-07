# STAR in place of MAY initials

Date: 7 November 2026. Status: investigation; no production policy change.
Language: ASD-STE100 Simplified Technical English. Runtime source: `7069fe2d7`;
repository HEAD: `dd9059f1e`.

**The FLOW-only change fixes the original four-method loop reproducer.**
It reports the finding in run-3 and stops normally at run-5. The full-mark
conversion also passes that case. The production implementation is unchanged.

The two MAY initial-emission cells can be changed in one central policy. It is not a
tail rename: a converted FLOW initial starts NORMAL and can produce a saved
NORMAL relation. A converted concrete initial stays DEMAND. A full-mark
conversion also has a measured storage cost risk.

This document distinguishes initial commands from submitted facts. Removing
MAY initials does not remove MAY facts, demand patterns or field-limit cuts.
`[any]` means MAY. `[any-taint]` means MUST and is a different tail.

## 1. Complete native emitter inventory

The live policy is
[`RestrictedInitialPolicy.kt`](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/RestrictedInitialPolicy.kt).
After its base, mark, budget and legal-shape checks, only these two cells
return an initial with the MAY tail. Let `p` be the demand path, `q` the
submitted path, `F` the abstract FLOW mark and `T` a compatible full mark.

| Demand | Submitted fact | Current initial | Proposed replacement |
| --- | --- | --- | --- |
| `x.p.[any]/M` | `x.p.[any]/T` | `x.p.[any]/M` | `x.p.*/M` |
| `x.p.[any]/M` | `x.q.[any]/T`, where `q` is a strict prefix of `p` | `x.p.[any]/M` | `x.p.*/M` |

`M` is either `F` or the required compatible full mark. The submitted mark
can also be FLOW when the demand accepts FLOW. Exclusions are empty in
these MAY cells. All selected paths must fit the current field limit.
Both cells apply in forward and backward restricted runs, starting at run-2.

Examples of the second cell are demand `x.f.[any]/F` and submitted
`x.[any]/T`. It emits at `x.f`, not at `x`. Conversion needs no extra field.

The native entry routes all use this policy:

```text
method call:
  limit submitted facts -> DemandStore.initials -> InitialDemandResults.offer
  -> RestrictedInitialPolicy.emitAdmission -> callee start

local block or loop:
  physical block-entry demand -> the same policy -> block start

run-2 static demand completion:
  local/transitive demand lookup -> the same offer/policy -> start
```

There is no separate native MAY emitter in one of these routes. Run-1 raw
inputs, mark answers and static point resumes select ZERO, EXACT or STAR
initials. Run-1 validation rejects MAY and MUST initials.

The initial interner can represent MAY, but it does not start an analyzer.
Summary premise keys, transient record views and loop observation queries
must not be counted as extra entry emitters. An existing MAY command can be
replayed at another reached physical entry; that replay creates no new shape.

The following cells are outside this replacement:

- EXACT and first-new-field refinement outputs keep their current behavior.
- MUST inputs keep their MUST rule, including the backward restriction.
- ZERO, static field anchors and exact class markers keep their grammar.
- Incompatible marks still emit nothing.
- MAY demand with a submitted STAR at the same path still emits nothing.
  Replacing an existing output does not change this rejected cell.

## 2. State the new start relation and layer

The candidate uses the current start factory after it replaces the tail.
It changes the initial key and the started fact together.

| Mark | Current command/start | Converted command/start |
| --- | --- | --- |
| FLOW | `p.[any]/F`, DEMAND | `p.*/F`, NORMAL |
| Full `T` | `p.[any]/T`, DEMAND | `p.*/T`, DEMAND |

The FLOW row is a major semantic change. It introduces a conditional NORMAL
relation for analysis; it does not make the caller's submitted MAY fact NORMAL.
The concrete row keeps its DEMAND layer but changes suffix correlation:

```text
old seed: p.[any]/T -> p.[any]/T, D  // independent output suffix
new seed: p.*/T     -> p.*/T, D      // same input/output suffix
```

For an ordinary copy, the new relation transports the actual suffix. It does
not assert T on every descendant. MUST remains the form for uniform taint.
The selected correlated-concrete spec already uses this STAR start contract;
it explicitly left later MAY initials unchanged. This candidate extends that
choice to the two restricted-emission cells.

Keeping the old DEMAND override for converted FLOW STAR is a different design.
It does not create the reusable NORMAL getter record. It also conflicts with
the current restricted-summary invariant that a FLOW/DEMAND result has an
uncertain MAY tail. The AP factory alone does not establish an engine policy.

### 2.1 The two strategies on the same operands

The only difference between the strategies is the concrete-demand rows.
Assume empty exclusions and a field budget that fits each provided path. Each cell shows
the emitted initial and its start layer; the added fact is unchanged.

| Added fact | Demand pattern | Current emission | FLOW-only strategy | Full strategy |
| --- | --- | --- | --- | --- |
| `x.[any]/T, D` | `x.[any]/F` | `x.[any]/F, D` | `x.*/F, N` | `x.*/F, N` |
| `x.[any]/T, D` | `x.[any]/T` | `x.[any]/T, D` | `x.[any]/T, D` | `x.*/T, D` |
| `x.[any]/T, D` | `x.f.[any]/F` | `x.f.[any]/F, D` | `x.f.*/F, N` | `x.f.*/F, N` |
| `x.[any]/T, D` | `x.f.[any]/T` | `x.f.[any]/T, D` | `x.f.[any]/T, D` | `x.f.*/T, D` |

The first two rows use the same-path cell. The last two use the ancestor
input cell. FLOW-only conversion selects by the **emitted/demand mark**, not
by whether the added fact happens to have a concrete mark.

For the getter itself, the added fact is `ret.[any]/F, D`, and the demand is
`ret.[any]/F`. Both strategies emit `ret.*/F, N`.

Some controls are identical under both strategies:

```text
added x.$/T, N;      demand x.[any]/T  -> x.$/T, N
added x.f.g.$/T, N;  demand x.[any]/F  -> x.f.*/F, N
added x.[any]/U, D;  demand x.[any]/T  -> nothing, when U != T
added x.*/F, N;      demand x.[any]/F  -> nothing
```

The second control is the existing first-new-field rule. No MAY initial was
emitted there, so neither strategy changes it. The last control remains a
rejected input even though a MAY input can emit a STAR initial.

## 3. Getter trace

This ordinary body is enough to show the relevant transfer. `N` means NORMAL;
`D` means DEMAND. The old B2 operands come from the recorded small reproducer.
The new transfer was also checked through native AP and persistence operations.

```java
// run-2 demand:    ret.[any]/F -> arg.g.[any]/F
// submitted:      ret.[any]/F, D
// old initial:    ret.[any]/F, D
// candidate:      ret.*/F, N
Object getG(Object arg) {
    return arg.g;
    // backward old:       arg.g.[any]/F, D
    // backward candidate: arg.g.*/F, N
    // g has length 1; limit 1 does not cut it.
}
// old summary:       ret.[any]/F -> arg.g.[any]/F, D
// candidate summary: ret.*/F     -> arg.g.*/F, N
```

The new NORMAL summary can be persisted. Its opposite-direction view is
`arg.g.*/F -> ret.*/F`. The native check applied that view to
`arg.g.[any]/T, D` and obtained **`ret.[any]/T, D`**. Thus the new NORMAL
relation did not upgrade the actual uncertain support.

The old getter summary is DEMAND and creates no such NORMAL record. Its MAY
tail was inherited from the initial; it was not a new field-limit cut at g.

## 4. Original four-method experiment

Two isolated copies are tested: convert FLOW results only, and convert all
MAY results. Both copies update the raw output-image predicate with the
emitter. All other production classes remain native. The original loop,
mapper branches, getters, source, sink, field-limit schedule and final
expected-one-report assertion remain unchanged. No guidance is injected.

| Policy | NORMAL findings | First reporting run | Latest reached/complete run | End reason |
| --- | ---: | --- | --- | --- |
| Current runtime, recorded control | 0; expected-one assertion fails | none | run-5 / run-5 | NO_DEMAND_EDGE |
| FLOW-only conversion, new experiment | 1; original assertions pass | run-3 | run-5 / run-5 | NO_DEMAND_EDGE |
| All MAY conversion, new experiment | 1; original assertions pass | run-3 | run-5 / run-5 | NO_DEMAND_EDGE |

The current control and its first rejected getter route are in the
[saved-record audit](../reports/bidirectional-getter-saved-record-gap-20261106.md).
The control was not rerun. Root ran the two candidates separately, with
frozen classpaths, loaded-class origin checks, one CPU and a 1 GiB child heap.
The original native program and both final assertions returned successfully.
Neither candidate admits the previously rejected same-path STAR input under
a MAY demand. That additional admission change is not needed for this case.

These are bounded native diagnostics, not new real-project measurements.
There is no new Conductor, Stirling-PDF, Thingsboard or OWASP result. In
particular, this does not identify the first lost fact for the separate
Stirling-PDF License finding.

## 5. A negative workload effect for full-mark conversion

The following construction uses ordinary strong field writes and a selected
EXACT-root cleaner. The native AP/store test derives protection from the
cleaner. It does not insert a protection flag by hand.

```java
// A configured AnyField pass sends an exact source T into bag.[any]/T, D.
consume(bag);

// Current initial: q.[any]/T, D. Candidate initial: q.*/T, D.
void consume(Box q) {
    cleanRootT(q); // Selected T at the exact root; surviving T is protected.
    if (c1) q.f1 = null;
    if (c2) q.f2 = null;
    if (c3) q.f3 = null;
    if (c4) q.f4 = null;
    if (c5) q.f5 = null;
    sinkAnyT(q);
}
// Native joined store after each optional write:
// MAY:  1, 1, 1, 1,  1,  1 protected header
// STAR: 1, 2, 4, 8, 16, 32 protected headers
```

MAY clears field exclusions. STAR preserves each exclusion subset. The
selected protection contract retains those literal tail/exclusion headers,
so ordinary DATA merging cannot remove them. All paths remain at the same
depth. The 32 variants are not caused by a greater field limit.

This is a measured conditional AP/store cost difference. It does not prove
a complete program loses a finding or runs slower. It is not a measured cause
of Conductor or Stirling-PDF performance. FLOW-only conversion leaves this
concrete-MAY cell unchanged.

## 6. Required coordinated changes

A production proposal must include the following contracts together:

```text
emit(demand, actual):
    raw = currentEmit(demand, actual)
    if raw is absent: return absent
    if selectedForConversion(raw): return raw.withTail(STAR)
    return raw

canEmitInitial(demand, initial):
    test the exact image of the new emit operation
    remove converted MAY outputs
    admit same-path STAR under a MAY demand for converted marks
    retain all other existing image cells and shape/budget guards
```

Changing only `emit` violates its image contract. Current paired summary
restriction rejects converted concrete STAR keys. FLOW has a separate
normalized-EXACT preimage fallback, so its old C5 behavior differs. The isolated
copies change the image too; they do not treat this partial-patch rejection
as a counterexample to the coordinated candidate.

C5, prepared output tickets and Target entry checks consume that image.
They must keep the same paired exit, whole original, physical entry and
field-budget rules. A valid new entry is not permission for any exit.

Loop observations query C2 too. The current fast certificate explicitly
requires a MAY/DEMAND emitted witness. Converted STAR fails that test and
uses the ordinary trial fallback. A selected implementation must either
reprove the certificate for the new image/layer or accept and measure this
fallback cost. It must not change only delivered entry commands and leave
the read-only observation policy stale.

Two old initial commands can map to one STAR command. Caller subscriptions
are installed before callee start. Local block links and physical entry
identity are also retained before initial deduplication. Thus this collision
alone is not a lost-caller bug; identical new conditional analysis can be
shared. It does not prove whole-driver equivalence with the old policy.

Do not change all interned MAY keys. Some are summary premises or observations,
not start commands. Do not convert submitted MAY facts, demand patterns, MUST,
or field-cut results as part of this change.

## 7. Proof and test scope

Root checked 26 constructive Lean laws for this investigation. The model
proves the exact candidate image through executable old-emission witnesses,
base/path/mark preservation, unchanged MUST, budget cells, local layer and
Target guards, the certificate mismatch and a finite exclusion-family model.
Only `propext` and `Quot.sound` occur in the axiom audit.

Root also ran five native AP/store tests: **5 passed, 0 failed, 0 skipped**,
with 26 typed trace events. They cover layers, the old C5 image mismatch,
ordinary getter persistence/opposite replay, the 1-versus-32 header family
and unchanged inner MAY-demand/STAR-input rejection.

Both original-program candidates then passed independently. The AP getter
trace tests the proposed mechanism directly. The full-program results show
recovery of the original finding; they do not record every intermediate
candidate C2 callback or establish which changed callback was first.

These laws are not a whole-analyzer proof. Native static anchors, ND, aliases,
all physical ports, producer effects and global refinement/progress still
need coverage before production selection. No universal FP, FN, termination
or performance claim follows from a local shape/image proof.

The first proof attempts failed on the external Lean module root and a
reserved proof-local identifier. Root retained both failures. The successful
attempt only fixed module-root arguments and renamed that proof-local
identifier; it did not change theorem statements or definitions.

## 8. Assessment

The FLOW change directly addresses the getter's missing reusable relation,
and its isolated implementation recovers the original finding.
It is a coherent design candidate when emission, image, layer and loop
observation handling agree. It is not a one-line representation optimization.

Removing all MAY initials also changes concrete storage behavior. The native
protected-header example is sufficient to reject a claim that this blanket
change has no negative workload effects. It does not establish an inevitable
correctness defect. A production decision must state whether it selects
FLOW-only conversion or the full conversion and its storage cost.

**Recommended next design: convert the two FLOW/MAY emission cells to STAR,
with the current intrinsic NORMAL start and the coordinated image update.**
Keep the other admission cells unchanged. Specify the loop certificate update
or its fallback explicitly. Treat full-mark conversion as a separate extension;
its measured protected-exclusion cost needs an explicit storage decision.

This recommendation is not a proof that no other program can regress. No
correctness counterexample to the coordinated conversion was found in these
bounded tests. A full soundness/progress proof remains open.

The analyzer implementation and its normative specification remain unchanged.

## 9. Portable evidence

The [embedded evidence](../reports/data/bidirectional-star-initial-emission-audit-20261107.json)
contains the inventory, checked Lean source and checker, failed and successful
proof logs, native test source/receipts/XML/typed traces, both exact candidate
diffs, the byte-identical program, wrappers, classpath/source pins and complete
candidate console/results. It also contains the root ABI and terminal review.
No compiled binary, heap snapshot or raw profile is needed to read the report.
