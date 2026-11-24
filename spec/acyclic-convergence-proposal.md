# Acyclic convergence for the bidirectional analyzer

Status: FINAL for this round, 24 November 2026 (revision 2 with the
additions of 24 November). Final classification: group A (works) and
group B (questionable), in the section after this header. Decisions of 24
November in §1; clarifications in §5.2-§5.4; owner cover in §5.7.
It follows the
[design guide](design-guide.md). Revision 1 was condensed from
[natural-termination-proposal.md](natural-termination-proposal.md) §5.

Changes in revision 2:

1. Each rule has a formal definition and a real example (§5).
2. The acyclic scope has a formal definition (§3).
3. The proposal is standalone. The rules act on the native runtime: the
   native stop (`RUN_LIMIT` at run-11), no canonical order, no
   `FIXED_POINT`, no cycle fold W. All measurements are new (§6).
4. The C5 rule (`acC5Exact`, revision 1 §3.6) and its block form C5B
   (revision 1 §3.7) are withdrawn. The relative C5 cap makes only
   passenger rows (§5.6).

All rules are native prototypes behind flags on the local branch
`proto/acyclic-only-20261123`. None is merged.

## Final classification (24 November)

The work stops here. Gate for this classification: confirmed and
provisional results and SARIF code flows identical to native, and, by the
decision of 24 November, no rule may stop the refinement that serves a
second NORMAL route to a sink (§5.7, "Route condition"). Group A meets the
gate on all evidence and has no open precondition. Group B does not, or
is not shown to. The rules of the natural-termination proposal are
classified in that proposal (§0.1) with the same gate.

**Group A: works without negative consequences (on all evidence).**

| Rule | Evidence | Note |
| --- | --- | --- |
| §5.1 G6 drop form | Prefix closure on 29 JIR types (0 breaks, native 1,114). Alone: module, jvm, rule suite, OWASP identical except the decided removals (M4, D5, D6, boxed String chains). Sink routes: only the decided M4 removal differs from native. Never acts on OWASP; on Stirling-PDF and Conductor it removes 0 marks. | A decided semantic correction (20 November): it makes the mark policy monotone in K. It removes nothing else. |
| §5.5 EXACT cleaner on a MUST leaf | Alone: rule suite and OWASP identical (OWASP residual 711-735 → 24, the largest single effect); module: the four changed fixtures only (signed off 24 November); jvm: 6 of 6 analyses identical, 2 cleaner-table tests assert the old semantics. | Approved as semantics (24 November): an EXACT cleaner does not split a MUST region. The cleaned point stays tainted inside the region, so the rule can confirm a report that native keeps provisional; this is the intended result, not a negative consequence. Its own route changes are intended by the same decision (not measured alone). |

Implementation proposal for group A:
[acyclic-group-a-implementation.md](acyclic-group-a-implementation.md).

Not rules, safe to keep because they change no run when off (and only log
when on): the acyclicity oracle (§3) as a diagnostic, the AC residual
counter, the width census and MUST-cover drop log
(`proto/must-cover-shape-20261124`), and the sink-route census
(`proto/dt-owner-route-20261124`). The sink-route census is the check for
the route requirement; group B rules must pass it before they can move to
group A. Decided "no rule": the relative C5 cap stays native (§5.6).

**Group B: questionable.**

| Rule | Why it is in group B | What would move it to group A |
| --- | --- | --- |
| §5.2 X | Reports and code flows identical, but it stops serving a second route to a confirmed sink: `DistinctMarkOriginServiceTest`, `UniformCoverageOriginAuditTest`, `RecursiveWrapperTerminationTest` end early and do not serve the second route (§5.7). Its argument covers targets only, and it needs G6. | A route-exact condition (see owner cover) and a clean sink-route census. |
| §5.3 RX | The argument of X at a relay, so the same route question. The tag splits DemandTarget rows, relays and ND joins per report id (58 module tests compare the untagged object). In run-1 a tag changed NORMAL routes of static fixtures (measured with the owner-cover tag; RX also tags in run-1). | As X, and no tag in run-1. |
| §5.4 MUST-cover | The acyclic scope is a proxy (§5.4): without it Conductor widens its DEMAND summaries 2.2 times; the cover fix and a MAY-only restriction do not prevent it. Exact only for the NORMAL facts of the run where it acts. The prototype cover test has a defect (§2 item 3). | A form that does not change later demand, or withdrawal. On OWASP it only closes three `doSomething` helpers. |
| §5.7 owner cover | First form rejected (it stops serving second routes). With the route condition it keeps every fixture route, but OWASP still loses 19 NORMAL routes and the rule has almost no effect. | A K-saturation condition (drop only where nothing in the owner's analysis under the premise was bounded by K), or withdrawal. |
| AO-C5 (the combination of §5.1-§5.5) | Reports and code flows identical, but it changes 1,552 of OWASP's NORMAL sink routes (1,391 only in native, 161 only in AO-C5). The share of each member is not measured; part of it is the approved cleaner semantics. | X, RX and MUST-cover in group A, or out. |

Consequence for requirement AC: with group A alone, AC is not met. The
cleaner rule alone takes the OWASP residual from 711-735 to 24 (§5.5); G6
and the cleaner rule were not measured as a pair; no group-A
configuration is shown to empty the acyclic residual. Every measured way to close the
acyclic residual so far removes demand whose refinement still serves
NORMAL routes. The open direction is a K-saturation condition: demand may
go only where the owner's analysis no longer depends on K (§5.7,
conclusion 2), which is the premise of AC.

## 0. Summary

The verdicts in this section are the report gates of 23 November, before
the route requirement of 24 November. The final classification above
supersedes them.

Five rules. Each one removes one maker of acyclic demand at its source.

| Rule | Where it acts | Maker it removes | Alone against native: reports | OWASP AC residual alone (native 711-735 rows) |
| --- | --- | --- | --- | --- |
| §5.1 G6 drop form | type filter at a boxed level | none (prerequisite of X and RX) | identical | 729 |
| §5.2 X | forward DEMAND sink witness | DemandTarget renewal at a sink whose owner has a complete ZERO target | identical | 39 (with §5.1) |
| §5.3 RX | relay of a tagged DemandTarget | the same, relayed into a caller | identical | 39, all forward rows 303 → 227 (with §5.1, §5.2) |
| §5.4 MUST-cover | DEMAND reply at a call to an acyclic callee | a DEMAND reply that a NORMAL MUST reply covers | identical | 705 |
| §5.5 EXACT cleaner ignored on MUST | cleaner on a MUST leaf | cleaner survivor | identical, except 4 module fixtures (signed off 24 November) | 24 |
| §5.6 relative C5 cap | — | none: a passenger | — | — |
| §5.7 owner cover (proposed 24 November) | outgoing DemandTarget row at the forward barrier | DemandTarget renewal at an owner with a NormalTarget whose premise the DemandTarget premise implies | first form: identical, but loses second routes (rejected); with the route condition: identical, 19 OWASP routes still lost | first form 0; with the route condition 585 (§5.7) |

Combined (configuration AO-C5 = §5.1-§5.5), against native:

| | Native | AO-C5 |
| --- | --- | --- |
| OWASP (3 launches) | `RUN_LIMIT` 11; driver 150.2-153.1 s; residual 711-735 | `RUN_LIMIT` 11; driver 110.7-112.8 s; residual 6 rows / 1 owner; reports identical |
| Stirling-PDF (2 launches) | run-11 stalls: completes after 2,704 s, or times out at 3,000 s; residual 49 | `RUN_LIMIT` 11 after 55.7-56.0 s; residual 5 rows / 3 owners; reports identical to the completed native run |
| Conductor (1 launch) | timeout in run-8; H7 at 666 s; residual 21 (H7) | timeout in run-8; H7 at 600 s; residual 16 rows / 6 owners (H7); reports identical |
| Module suite | 30 analyses / 81 rows open | 18 / 47; 4 cleaner fixtures change (signed off) |
| Rule suite (585) | 2 / 9 | 1 / 8; reports identical |

Driver times include the residual diagnostic (§6). Requirement AC is not
met yet. The open makers are the inside read, the DEMAND STAR start and
alias self cycles that pass-through models make (§7).

## 1. Requirement

**Assumption.** JVM pass rules have no `[any]` in `from` or `to`. Source
and sink conditions with `[any]`, and conjunctions, are allowed. They make
MAY facts in backward runs only.

**Requirement AC.** For each acyclic method or block (§3) there is a
forward run after which it has no row in any forward handoff. The callers
do not matter: if a method has no demand row, a caller's demand gets no C2
start there, and the caller replays the method's complete records. The
caller's own rows carry the caller's imprecision. No stop test and no
limit may give AC. The analysis itself must converge.

**Why it should be possible.** In acyclic code the depth of an access path
is bounded by the premise depth and the field writes of the cone. When K
is larger than that bound, no global cut happens. Then every remaining
DEMAND row comes from a maker that does not read K. Under the assumption,
every such maker is made by the analyzer, so each one can be removed at
its source. The alias analysis can add field writes that the program
does not have (alias self cycles, §7 item 3). They make the bound larger
than the K of run-11, but they do not remove it.

**Gate.** Confirmed and provisional results must be identical to native,
by SARIF identity and code flows, on every project and suite. A change
that looks like a precision gain is a failure, because there is no
trusted ground truth. Time and peak memory must not be worse. Decided
exceptions: the G6 removals in synthetic fixtures (decision of 20
November) and the four cleaner fixtures of §5.5 (signed off on 24
November).

**Decisions of 24 November.**

| Decision | Effect |
| --- | --- |
| The C5 rule is removed | `acC5Exact` and C5B are withdrawn; the relative cap stays native (§5.6) |
| Keep the provisional results | The gate wins over AC. The inside-read rows of `UserService#saveUser` may stay; a rule for the inside read must keep the two Stirling-PDF provisional results (§7 item 1) |
| The four cleaner fixtures of §5.5 are signed off | Their new confirmed result and three provisional → confirmed changes are accepted |
| Robustness rule | The core must prevent fact explosion by itself, whatever the code under analysis, the rules or the alias analysis give it. The relative caps are this mechanism: C2 starts at most `FL(Dc)+1` deep and C5 publishes at most `FL(Dp)+1` deep, so a deep fact waits for the demand that asks for it. No rule may relax them on the basis of a property of the code or of an outer input |
| Serve every route | A rule must not stop the refinement that serves a second NORMAL route to a sink, also when the report and the code flows do not change (owner cover, first form, rejected). Measured with the sink-route census (§5.7) |
| Cleaner rule approved | The EXACT-cleaner rule (§5.5) is approved as semantics; it is in group A |
| Stop and finalize | The rules are split into group A (works) and group B (questionable); see the final classification |

## 2. Notation

**Leaf.** A DATA leaf is `λ = ⟨β, π, τ, μ, E, ℓ⟩` and a protection flag.

| Part | Meaning |
| --- | --- |
| `β` | The base: `arg(i)`, `this`, `ret`, a local `var(i)` or a static class. |
| `π = a1…an` | The accessor chain: named fields and the array element `[]`. `FL(π) = n`. `FL` does not count the tail, the base or the static class accessor. |
| `τ` | The tail: `$` (EXACT), `*` (STAR), `MAY` (`[any]`), `MUST` (`[any-taint]`). |
| `μ` | A concrete mark `T`, or `FLOW` (the abstract mark of a relation). |
| `E` | The exclusion: a set of first accessors below `π`. |
| `ℓ` | The layer: `N` (NORMAL) or `D` (DEMAND). |

**Region.** `R(β.π.$) = {π}`. For `τ ∈ {*, MAY, MUST}`:
`R(λ) = {π} ∪ {π·a·σ | a ∉ E}`. A `MUST` leaf states that every path of
its region holds `μ` (a uniform region). A `MAY` leaf states that some
path of its region can hold `μ`. A cut makes a `MAY` tail on layer `D`.

**Cover.** `μ ⊒ λ` (the leaf `μ` covers the leaf `λ`) when they have the
same base and mark and `R(λ) ⊆ R(μ)`. For a `MUST` leaf `μ` this is:

1. `π(μ)` is a prefix of `π(λ)`;
2. if `π(λ)` is longer, `E(μ)` admits the accessor of `π(λ)` at position
   `|π(μ)|`;
3. if `π(λ) = π(μ)` and `τ(λ) ≠ $`, then `E(μ) ⊆ E(λ)`.

**Owner and summary.** An owner is `o = (m, s)`: a method `m` and a block
scope `s` (`s = root` for a method with no loop). A summary of `o` is
`P → C`. The premise `P` is ZERO, one initial, or an ND conjunction of
initials. The conclusion `C` is DATA facts or a target. ZERO is the empty
conjunction: `P ⊨ ZERO` for every `P`. So a summary at ZERO holds in
every entry state. A complete summary is on layer `N`.

**Targets.** `NormalTarget(id)` is a complete source-to-sink proof of the
report identity `id = (method, sink node, rule)`. `DemandTarget` is a
sink hit on layer `D`, or a backward source discharge. It asks the next
runs to refine its premise.

**Runs.** Forward and backward runs alternate. Run-1 is forward. The
field limit is `K = 1, 1, 2, 3, …`. At the barrier of run `i` the handoff
`H_i` holds the demand rows of run `i`: DEMAND summaries, ND summaries,
backward ZERO summaries (`ap/Demand.kt:136-140`) and outgoing
DemandTargets (`driver/HandOff.kt`; in restricted runs only the targets
that `acceptsTarget` admits). Run `i+1` reads a row `r` as a pair: the
entry selector `Dc(r)` and the exit pattern `Dp(r)`.

- **C2** admits a start under `Dc(r)` with a depth of at most
  `min(K, FL(Dc)+1)`.
- **C5** selects a raw conclusion against `Dp(r)` and cuts it at
  `min(K, FL(Dp)+1)`. This is the *relative cap*. A conclusion below
  `Dp` is kept; a `MAY` or `MUST` conclusion above `Dp` is moved down to
  the path of `Dp`; a `*` conclusion above `Dp` is kept whole at its own
  path (`ap/Reference.kt:245-253`). Each row whose entry is a prefix of
  the premise member and whose exit overlaps the output selects and cuts
  for itself. C5 publishes the union (`store/DemandStore.kt`, `intersect`
  and `offerDataPair`).

File paths are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`,
and line numbers refer to the prototype branch, unless a section names
another commit.

**Stores.** `NT(o)` = the saved complete target summaries of `o` (they
persist across runs) and the target summaries that `o` emitted earlier in
the current run. `Rec(g)` = the saved NORMAL records of the method `g`.
Saved replay applies `Rec(g)` at each call offer before the offer
subscribes to the current publications of `g`.

**AC residual.** `Res_i` = the number of rows of the forward handoff
`H_i` whose owner is acyclic (§3). This revision gives it in rows and in
owners.

## 3. Acyclic scope

### 3.1 Definition

Let `CG = (M, →)`. `M` is the set of method keys with a body that the
analysis reads: application code and analysed approximation bodies. A
method key is a method in a context (the JVM key is the entry point of a
method context, `JIRCallPlanBuilder.kt:310-311`), so the scope is decided
per key. `m → n` when a call instruction of `m` has `n` in a
`CallStage.Callees` stage of its forward call plan
(`interp/CallPlan.kt:215`). A model without a body is not in `M`. A call
to it adds no edge: it is a leaf.

`Loop(m)` holds when the block layout of `m` has a LOOP block. The layout
builder turns every cycle of the instruction graph of `m` into LOOP
blocks (one strongly connected component can give nested LOOP blocks),
and it checks that no cycle is left outside the loop blocks
(`org/opentaint/dataflow/graph/MethodBlockLayoutBuilder.kt:35-76`,
`:152`). So `Loop(m)` holds exactly when the instruction graph of `m`
has a cycle.

```text
Cyclic(m)  ⟺  ∃ n:  m →* n  ∧  ( Loop(n) ∨ n →⁺ n )
Acyclic(m) ⟺  ¬Cyclic(m)
```

The same set as a least fixed point over the condensation of `CG`:

```text
Acyclic(m) ⟺ ¬Loop(m) ∧ ¬(m →⁺ m) ∧ ∀ n: (m → n ⇒ Acyclic(n))
```

**Fail-safe.** When the layout, the forward graph or a call plan of `m`
cannot be read, `Cyclic(m)`.

**Block form.** A block `b` of the layout of a method `m` is acyclic,
`AcyclicBlock(m, b)`, when all of these hold:

1. `b` is not the root block;
2. `b` is not a LOOP block, and no block in the subtree of `b` is a LOOP
   block;
3. no ancestor of `b` is a LOOP block;
4. `b` is not, and no ancestor of `b` is, the `after` child of a
   sequential block that has a `loop` child (no loop comes before `b`);
5. every call instruction of `b` has only acyclic callees.

An owner `(m, s)` is acyclic when `s = root` and `Acyclic(m)`, or
`s = b` and `AcyclicBlock(m, b)`.

### 3.2 Implementation

`engine/AcyclicScope.kt` on the prototype branch: one oracle per
analysis, made on first use.

- Reads: `MethodBlockLayout.hasLoops`, the forward graph, and for each
  call instruction the `CallStage.Callees` of its forward call plan with
  the FULL rule view (`AcyclicScope.kt:128-157`).
- Walk: iterative Tarjan over `CG`, no recursion (`:179-235`). A completed
  strongly connected component is final and memoized.
- Fail-safe: an exception in a read, or a walk that does not complete,
  makes the method cyclic (`:130-147`, `:164-171`). A cancellation is not
  caught.
- Counts per analysis (`BIDI_AC_ORACLE`): OWASP 7,414 methods (2,196
  cyclic, 5,218 acyclic), Stirling-PDF 4,392 (978 / 3,414), Conductor
  13,861 (3,467 / 10,394). No read failed on any measured analysis, so
  the fail-safe form changed no decision.

### 3.3 Properties

- **Static.** The call plans come from cached rule forms
  (`interp/FormsCache.kt:131-186`), and the layouts from the method
  context cache (`MethodContextCache.blockLayout`; JVM
  `JIRMethodContextCache.kt:19-20`). Their inputs are the program, the
  rules and the rule view. They do not read the run, K or the demand. So
  the scope of a method is the same in every run (INFERENCE from code).
- **Where the scope is read.** Only the MUST-cover rule (§5.4) reads it,
  as `Acyclic(callee)`. The residual counter also reads it, as a
  diagnostic. With the C5 rule withdrawn (§5.6), no other rule reads it.
  The scope only limits where MUST-cover removes a reply. A wrong scope
  cannot add a fact, so the robustness rule (§1) holds.
- **Robustness check of the five rules.** No rule relaxes a relative
  cap or the global limit. G6 removes marks; X and RX remove targets and
  seeds; MUST-cover removes replies; the cleaner rule keeps a leaf
  unchanged. None of them makes a fact deeper or makes more facts.
- **Cost.** One walk per analysis, memoized, `O(|M| + |→|)` reads. When the
  residual counter classifies every owner, the walk costs 15.5-15.8 s on
  OWASP (most of it at the run-1 barrier) and 2.2-2.5 s on Stirling-PDF
  and Conductor. The cost of the MUST-cover queries alone was not
  measured (§11).

## 4. Makers of acyclic demand

An *anchor* keeps rows alive by itself. A *passenger* lives only while an
anchor of another class acts in the same owner. Sources: the shadow
census of revision 1 (`proto/acyclic-census-20261120`) and the lineage
diagnostic of §5.6. Natively 350 acyclic OWASP owners never reach zero
rows (164 `doPost`, 164 `doGet`, 22 `doSomething`), about two thirds of
OWASP's open demand.

| Maker | Class | Where it shows | Rule | Status |
| --- | --- | --- | --- | --- |
| DemandTarget renewal at a sink whose owner has a complete ZERO target | anchor | 919 forward rows at 431 OWASP roots: a closed two-run cycle with no DATA row | X (§5.2), needs §5.1 | selected |
| The same, relayed into a caller with a complete ZERO target | anchor | Stirling-PDF `bytesToWebResponse` relays | RX (§5.3) | selected |
| A DEMAND callee reply that a NORMAL MUST reply covers | anchor | OWASP `doSomething` families | MUST-cover (§5.4) | selected |
| Cleaner survivor: an EXACT cleaner inside a MUST region | anchor | DemandTarget witnesses at 151 of 164 OWASP roots; `Thing2` | §5.5 | selected |
| Read at a strict prefix of a premise ("inside read") | anchor | OWASP `BenchmarkTest01874#doSomething`; Stirling-PDF `saveUser`; Conductor `Optional#map` lambda | — | open (§7 item 1) |
| DEMAND STAR start: a STAR start with a concrete mark is DEMAND by itself | anchor | Stirling-PDF `AuthController#login` (from a backward MAY row); 10 module fixtures (from an ANY entry) | — | open (§7 item 2) |
| Alias self cycle: the local alias analysis puts an object and one of its fields in one alias group, and the ALIASES call stage writes the object below itself (up to 6 levels per call) | global cut while K is below the bound | Conductor `ExclusiveJoinTaskMapper#getMappedTasks`; 7 Stirling-PDF owners; 12.6 % of OWASP call plans have a self alias | — | open (§7 item 3) |
| Relative C5 cap `FL(Dp)+1` | passenger | OWASP helpers; Conductor `Optional#map`; Stirling-PDF `decodeMimeHeader` block 1 | none (§5.6) | no rule |
| Complete backward-ZERO and ND rows | passenger | 730 backward rows on OWASP | none | they follow the DemandTarget cycle |

## 5. Rules

Each rule has a flag and is off by default. With every flag off the
module suite (2,765 tests) and the jvm suite (473 tests) pass, and no
runtime path changes. Each "Gate alone" line compares the rule (with its
prerequisites) with native on the module suite (314 analyses), the jvm
suite (6 analyses), the rule suite (585 analyses) and one OWASP launch.
Driver times include the residual diagnostic; native is 150.2-153.1 s.

### 5.1 G6 drop form (prerequisite of X and RX)

Flag `-Dorg.opentaint.bidi.g6Drop=true`. Decision of 20 November.

**Definition.** A type filter with a mark policy acts on a TAINT tree
whose value has the static type `τ`. The spine levels `k = 0, 1, …` are
the nodes `β.[]^k`. `τ_k` is the type at level `k`. `Boxed(k)` holds when
`τ_k` is a class that unboxes to a primitive (`Integer`, `Long`,
`Boolean`, `Character`, …). `drops(t, k)` holds when the policy does not
keep the mark `t` at the boxed level `k` (`t` is not primitive-tracking).
Let `k0` be the first boxed level. For `j ≥ k0`:

```text
D_j = { t ∈ marks(subtree at []^k0) | ∃ k: k0 ≤ k ≤ j ∧ Boxed(k) ∧ drops(t, k) }
```

- Native: at each spine level the filter removes marks only from the
  leaf of that level (`ap/Filter.kt`, `markPolicyOnElements`). Field
  subtrees below a boxed level, for example `[]^k.value`, keep their
  marks.
- Drop form: at each spine level `j ≥ k0`, remove `D_j` from the spine
  leaf and from every leaf of every field subtree of level `j`
  (`ap/Filter.kt` `markPolicyDropForm`, `dropOnValue`). Levels above `k0`,
  and policies with no boxed level, keep the native result.

**Property (prefix closure, ap.md §5).** For a path `p` at or below a
boxed level, the filter removes `t` at `β.[]^k.p` if and only if it
removes `t` at `β.[]^k.q.MAY` for every prefix `q` of `p`. So the result
for a mark does not depend on the cut depth, and the filter is monotone
in K. `JIRG6DropPrefixTest` checks this on 29 real JIR types and all
paths of length 3 or less: native has 1,114 breaks, the drop form 0.

**Example (reduction, fixture M4).** `x` has the type `Integer[]`. A
source writes `T` into `x[].value`. `T` is not primitive-tracking. At
`K = 1` the fact is cut to `x.[].MAY/T`, a spine leaf of the boxed level
1, and native drops it. At `K = 2` the fact `x.[].value.$/T` is a field
leaf below the boxed level, and native keeps it. So the sink is reached
at `K = 2` and not at `K = 1`: native is not monotone in K. The drop form
drops the mark at every K. This removes finding B of M4, D5, D6 and 13
boxed String chains, as the decision expects.

**Real code.** The drop form never applies on OWASP or the rule suite.
It applies 736 times on Stirling-PDF and 2,075 times on Conductor, each
time with 0 marks to remove.

**Gate alone.** Module 314 of 314 identical; jvm 6 of 6; rule suite 585
of 585; OWASP identical, 152.3 s, residual 729. The DECIDED-era fixtures
M4, D5, D6 were not ported to the branch; their result is from revision 1.

### 5.2 DemandTarget subsumption X

Flag `-Dorg.opentaint.bidi.dtSubsumption=true`.

**Definition.** Let `w` be a sink witness in a forward run at the owner
`o = (m, s)` with the report identity `id`. Let `(P, D)` be its DEMAND
arm. In restricted runs `P` is the union of the witness origins.

```text
native:  emit  P → DemandTarget   and capture the sink seeds S(w)
X:       if (ZERO → NormalTarget(id)) ∈ NT(o):  emit nothing and capture nothing
```

X decides once per witness, at its first DEMAND arm. NORMAL arms do not
change. Backward runs do not change.

**Report identity (24 November).** X needs no tag. The witness knows
its own identity `id = (method, sink node, rule)`
(`engine/RunMethodLocalServices.kt:373`), and X tests
`ZERO → NormalTarget(id)` for this `id` only (`:387`). Another sink
`id2 ≠ id` in the same owner has its own witness. X tests
`NormalTarget(id2)` there, and that witness keeps its DemandTarget and
its seeds while `id2` has no complete ZERO target. A seed names its rule
and its sink statement (`Seed.Sink(rule, method, at, pattern)`,
`driver/HandOff.kt:247-252`), so X removes only the seeds of `id`.

The identity is lost only after the emission. Natively
`P → DemandTarget` has no identity. So the witnesses of `id` and `id2`
with the same premise make one target row, and one handoff row
`(Target, member of P)` for each member (`driver/HandoffCompactor.kt:127-131`).
When X suppresses the witness of `id`, the witness of `id2` still makes
this row, and `id2` needs it. The next runs refine `P` for `id2`. This
work can reach the sink of `id` again, and X suppresses that witness
again. So the demand for `id` does not stay alive by itself; it is a
passenger of the demand for `id2`. The lost identity matters only at a
relay (§5.3).

**Exactness argument.** `P ⊨ ZERO`. The DemandTarget and the seeds ask
the next runs for a NORMAL proof of `id` at `o` under a refinement of
`P`. Every result of that work is a row `P' → NormalTarget(id)` at `o` or
above, and `ZERO → NormalTarget(id)` implies each of them. ZERO needs no
binding, so every caller of `o` relays the complete target. The argument
needs one more property: every sink that a later run can confirm keeps
its own witness and seed. So the analysis must be monotone in K, and X
needs §5.1 (without it, 17 module analyses lose finding B).

**Example (OWASP `BenchmarkTest00452#doPost`, an acyclic root).** The sink
is the conjunctive path-traversal sink at
`new FileInputStream(file.toString())`. The cleaner survivor (§5.5)
gives the fact `arg(0).MUST/T,D` at the sink, so the witness has a DEMAND
arm in every forward run. Native emits a DemandTarget and captures the
seed. The backward run starts at the seed and makes the ZERO rows of the
root again. These rows admit the next DEMAND hit: a closed two-run cycle
with no DATA row. The root already has the saved
`ZERO → NormalTarget(id)` from an earlier run. X suppresses the
DemandTarget and the seed. The backward run then makes no row at the
root, C2 admits no ZERO start there, and the root is not analysed again.
Natively OWASP has 919 such forward rows at 431 roots. X closes 328 of
the 349 open acyclic owners.

**Gate alone (with §5.1).** Module identical, 20 analyses end earlier; jvm
6 of 6; rule suite identical, 3 end earlier; OWASP identical, 120.7 s,
residual 39.

**Cost.** Per forward DEMAND sink witness, at most three hash lookups.
OWASP 62,687 witnesses (34,892 suppressed); Stirling-PDF 2,353 (119);
Conductor 457 (0: no Conductor owner has the complete ZERO target).

### 5.3 Relay subsumption RX

Flag `-Dorg.opentaint.bidi.dtRelayCover=true`.

**Definition.** A witness `w` tags its DemandTarget with its report
identity: `DT(id)`. Relays keep the tag. A relay copies a target summary
of a callee into the caller owner `o'` at a call.

```text
native:  relay DT(id) into o'
RX:      in a forward run, if (ZERO → NormalTarget(id)) ∈ NT(o'):  do not relay
```

RX acts only at the relay through a call binding
(`engine/RunMethodCallServices.kt:527-529`). A block lift passes the
target on unchanged, with its tag (`engine/MethodBlockRuntime.kt:548-549`),
and RX does not act there. (The DemandTarget branch of the loop consumer,
`engine/LoopConsumerObservation.kt:85`, is reached only in backward runs,
from `engine/LocalRelationApplication.kt:157`; correction of 24
November.) So a tagged DemandTarget lifted from a block into a root that
has `ZERO → NormalTarget(id)` is still emitted at the root. Backward
source discharges are untagged and relayed as before.

**The tag (24 November).** Only RX needs the tag: the relay site sees
only the callee's target row `P → DemandTarget`, and that row has no
identity (§5.2). In a forward run every DemandTarget comes from a sink
witness (`engine/RunMethodLocalServices.kt:400`). The other DemandTarget
sites are backward source discharges. The tag lives in one forward run:

1. the witness makes `DT(id)`;
2. a call relay copies the target value
   (`engine/RunMethodCallServices.kt:499-530`); a block lift passes it
   on;
3. the handoff erases it. A target row projects to
   `(Target, member of P)` with no identity
   (`driver/HandoffCompactor.kt:127-131`), so `DT(id)` and `DT(id2)` with
   the same premise give the same handoff rows.

The next run, the backward runs and the stores never see a tag. The cost
of the tag as a target value: `DT(id)` and `DT(id2)` with one premise are
two target rows and two relays where native has one, and 58 module tests
compare the untagged object.

**Decision at the handoff (open, not measured).** X and RX decide during
the run, against `NT(o)` = the saved targets and the targets that `o`
emitted *earlier* in this run (`engine/DtSubsumption.kt:47-56`). So the
decision depends on the order of the work. The same decision can be made
once, at the barrier, against the complete `NT_i(o)` of run `i`. In a
restricted forward run (run-3 onward) a DemandTarget makes only relays
and handoff rows. It makes no DATA fact. So there a removal at the barrier
gives the same handoff as a removal during the run (INFERENCE from the
code: the forward consumers of a target are the call relay, the block
lift and the handoff). Run-1 is different: a DemandTarget whose premise
has a STATIC member goes through the static lane
(`engine/RunMethodCallServices.kt:533-543`) and can ask FLOW writers for
marks (`engine/Run1StaticService.kt:244`, `engine/Run1PointResume.kt:298-309`),
which makes DATA facts. So in run-1 the decision must stay in the run. The id of each row
must still reach the barrier, so the tag stays: the decision moves, the
tag does not go away. Seeds need the same: today the root and the block
scopes of a method share one seed set, and a seed records no owner
(`engine/MethodBlockRuntime.kt:235`), so a barrier rule that removes the
seeds of one owner needs the owner of each seed.

| Form | At the barrier of forward run `i`, drop | Difference from X + RX |
| --- | --- | --- |
| H-owner | each outgoing `DT(id)` row of owner `o`, and the seeds of each witness of `id` at `o`, when `ZERO → NormalTarget(id) ∈ NT_i(o)` | independent of order; includes X. But a `DT(id)` that RX stops at the caller `o'` still reaches the callers of `o'` during the run, and their rows stay unless their own owner is covered. The callers of `o'` do not always have the ZERO target: it does not relay into a DEMAND binding (`engine/RunMethodCallServices.kt:509`), and saved ZERO targets are not replayed at calls (`:353`) |
| H-lineage | as H-owner, and each row that a `DT(id)` reaches only through covered owners (needs the relay edges of the run) | equal to X + RX, plus block lifts; independent of order |
| H-global | each `DT(id)` row and each seed of `id` when `id` is confirmed | removes all demand for a confirmed `id`, also where the owner premise is not ZERO |

For H-global: at each forward barrier the report builder checks that
every retained method-scope `ZERO → NormalTarget(id)` has its id among the
confirmed results (`driver/Report.kt:58-60`;
`engine/NormalTargetStore.kt:19` keeps only method-scope rows). So "some
method has `ZERO → NormalTarget(id)`" is the same as "`id` is
confirmed". Block-scope ZERO rows are not in this check, so H-global is
defined by the confirmed set itself. H-global does not stop the analysis
and does not infer anything about another id. It removes work whose only
effect is on an id that is already confirmed. Its exactness argument is
the argument of X: by monotonicity in K, every other sink that a later
run can confirm keeps its own witness, DemandTarget and seed. Risks: the
SARIF code flows of a confirmed id, if the trace resolution uses NORMAL
targets that later runs add; and its closeness to the rejected
report-based stops. H-global is the only form that also removes a
DemandTarget whose owner premise is not ZERO, for example the block-3
DemandTarget of the OWASP `doSomething` families (§5.4).

**Exactness argument.** The argument of X, at `o'`.

**Example (Stirling-PDF).** `WebResponseUtils#bytesToWebResponse` has a
predicate sink (`xss#sink#1`). Its DEMAND arms make DemandTargets in
every forward run. `multiPartFileToWebResponse` relays them. Each of four
`FilterController` methods relays them again at premise ZERO, and then
its Spring entry point. Each `FilterController` method already has the
saved `ZERO → NormalTarget(72)` and `ZERO → NormalTarget(92)`. RX stops
the relay there. It also stops the relay into
`ConvertEmlToPDF#convertEmlToPdf` (premise ZERO, with a complete
`NormalTarget(72)`), whose backward work kept the EML pipeline open.

**Why not a wider cover.** A cover of an ND DEMAND arm by a complete
target at a subset premise loses `B@g:1` in fixture M3: that arm's
DemandTarget and seed are the only refinement channel for callers that
bind the premise on the DEMAND layer.

**Gate alone (with §5.1, §5.2).** Module identical, 21 end earlier, 58
more test failures than §5.2 alone: they compare the untagged
`DemandTarget` object (representation). jvm 6 of 6; rule suite
identical; OWASP identical, 120.5 s, all forward rows 303 → 227, residual
39.

**Cost.** One tag per sink DemandTarget; per tagged relay, at most three
hash lookups. OWASP 2,266 relays (187 not made); Stirling-PDF 20,319
(162); Conductor 104,122 (182).

### 5.4 MUST-cover reply rule

Flags `-Dorg.opentaint.bidi.mustCoveredReply=true` and
`-Dorg.opentaint.bidi.mustCoveredAcyclicOnly=true`.

**Definition.** A caller reference is
`ρ = (caller owner, caller premise π_c, caller layer ℓ_c, call c, stage)`
(`store/AddedFacts.kt:17`). It does not name the callee or the actual:
all callees of the call stage, and all actuals offered under `π_c`, share
it. In a forward restricted run let `Cov(ρ)` be the set of leaves `μ`
that saved replay has delivered at `ρ` so far in this run, with
`ℓ(μ) = N`, `τ(μ) = MUST` and a concrete mark. Saved replay here means the
native record lanes and the record views; pending-demotion lanes add no
leaf (`engine/RunMethodCallServices.kt:588, :608, :631-647`).

A current publication of a callee `g` with a single-initial premise and a
conclusion on layer `D` gives a result `f` at `ρ`
(`applySummary`, `:405-415`). Drop `f` when all of these hold:

1. `ℓ_c = N`, and the offered actual is on layer `N`;
2. `ℓ(f) = D` and `f` is not protected;
3. `∀ λ ∈ leaves(f) ∃ μ ∈ Cov(ρ): μ ⊒ λ` (§2);
4. `Acyclic(g)` (§3).

ND publications and static-group replies are never dropped. Saved replay
exists only in restricted runs, so the rule never acts in run-1. Saved
replay of an offer runs before the offer subscribes, so `Cov(ρ)` holds
the covers of the same offer when its current replies arrive. A reply
that arrives before the replay of another offer under the same `ρ` is
kept: the decision depends on the arrival order.

**Prototype defect.** The cover test of the prototype
(`mustCovers`, `engine/RunMethodCallServices.kt:672-678`) checks items 1
and 2 of §2 but not item 3: at equal paths it does not compare
exclusions. So `π.MUST{f}` "covers" `π.MAY`, whose region holds
`π.f·σ`. Fix the test before the rule lands, and gate again.

**Exactness argument.** The caller state at `ρ` is the union of all facts
delivered at `ρ`. In the run where the rule acts, a covered DEMAND leaf
adds no path and no mark to that union, because a NORMAL MUST leaf in it
already holds the mark at each path of the leaf's region (with item 3 of
the cover). So no NORMAL fact, record, target or report of that run
changes. Across runs it is not exact: on one OWASP entry native makes 6
more records and 4 more block targets in runs 5-8. No report changes.

**Example (OWASP `BenchmarkTest01000$Test#doSomething`).** The helper is
`bar = new String(decodeBase64(encodeBase64(param.getBytes())))`. Block 3
of `doPost` offers `arg(1) = var(27).MUST/T,N`. Saved replay gives
`ret.MUST/T,N`. The current DEMAND replies are `ret.MAY/T,D` (an inside
read of a coarse premise) and `ret.Y.MAY/T,D` (a relative C5 cut). Both
have the base `ret` and the mark `T`, and `ret` is a prefix of both paths,
so `ret.MUST/T` covers them. Natively the DEMAND fact reaches the sink and
makes `DemandTarget(var(27).MUST/T)` in every forward run. Its row renews
the block rows, the helper's coarse start and the inside read. With the
rule, the five helper families go from 103 / 154 rows (H7 / H8) to 0 from
H5.

**Why the scope.** Without condition 4 the Conductor H7 rows become 2.2
times native: nearly all drops there are in cyclic callees. With it,
Conductor keeps 29,795 covered replies of cyclic callees and drops 2.

**The scope is a proxy (trace of 24 November).** Branch
`proto/must-cover-shape-20261124`, report
`docs/reports/must-cover-shape-20261124.md`: Conductor launches up to H7
with a width census of each forward handoff and a log of each drop, one
launch per arm. VERIFIED:

- The unscoped rule drops 366 / 11,914 / 17,667 replies in runs 3 / 5 / 7.
  29,942 of 29,947 are replies of cyclic callees. 3,384 of them are the
  equal-path covers that cover item 3 rejects (the prototype defect
  above), all in `WorkflowExecutorOps`.
- H7 has 181,935 rows against 84,720 native, but the number of handoff
  origins is the same (11,924 against 11,830). The summaries are wider,
  not more: 197,486 projected rows against 92,068. Run 7 takes 385 s
  against 91 s.
- 105,123 of the 105,418 new projected rows (99.7 %) are in three
  owners: block 2, the loop body, of `ParametersUtils#replace` (two
  contexts) and of `ParametersUtils#replaceList`. The two methods call
  each other inside their loops.
- The rows change before the growth: H5 has 118 more rows (650 fewer
  projected rows) and H6 (backward) 11,891 fewer rows. Only run 7
  publishes the wider summaries.
- In `replace` block 2 the run-7 DEMAND leaves, summed over the
  summaries, grow from 68,773 to 166,148. Two kinds of leaves grow. (a)
  FLOW MAY leaves at depth 3 (`var(3).F1.F2.F3`, 10 × 10 × 42 fields):
  native has the same 4,105 distinct leaves, but the 36 summaries that
  carry them hold 2,687 each on average, against 631 in 41 native
  summaries (25,867 → 96,720). At the same time the FLOW MAY leaves at
  depth 2 go from 22,784 to 15,599. A MAY leaf subsumes every fact at or
  below its path in its layer (`ap/Reference.kt:586`), so the lost
  depth-2 leaves are the coarse leaves that held the depth-3 fan-out.
  (b) concrete EXACT leaves at depth 2 (`var(3).F1.F2.$`, 5 × 18 fields
  of pass-through models and one application field): 202 → 33,125, in
  735 summaries against 179. This is the model family of §7 item 3.
- The run-7 drops inside `replace` block 2 (1,208) are DEMAND replies of
  the recursive calls (`newValue = replaceList(…)`, `newValue =
  replace(…)`): 742 with MAY tails (`ret.MAY/T,D`, `arg(0).MAY/T,D`,
  `ret.Iterable#Element.MAY/T,D`), 414 with EXACT tails and 52 with MUST
  tails, covered by `ret.MUST/T,N`, `arg(0).MUST/T,N` and similar.

Two restrictions, measured on the same Conductor setup:

| Arm | Drops runs 3 / 5 / 7 | H6 rows | H7 rows | H7 projected | Run 7 |
| --- | --- | ---: | ---: | ---: | ---: |
| native | none | 149,621 | 84,720 | 92,068 | 91 s |
| unscoped | 366 / 11,914 / 17,667 | 137,730 | 181,935 | 197,486 | 385 s |
| unscoped, cover item 3 fixed | 372 / 9,938 / 16,297 | 137,658 | 182,023 | 197,780 | 270 s |
| unscoped, cover item 3 fixed, MAY-tail replies only | 170 / 7,102 / 11,606 | 137,530 | 183,832 | 201,289 | 266 s |

Both restricted arms grow in the same three owners. On OWASP (AO-C5,
one launch each) the cover fix and the MAY-only restriction change
nothing: the same 56 drops, residual 6, 2,633 / 0 and code flows
identical to native. Every AO-C5 drop on OWASP is a MAY-tail reply. AO-C5
without MUST-cover: reports and code flows identical, driver 112.2 s,
residual 24 instead of 6. The 18 extra rows are the DEMAND rows of
three `doSomething` helpers (`BenchmarkTest00996`, `01000`, `01009`; 6
each).

Conclusions:

1. Acyclicity does not separate the cases. Cycles do not make the
   growth; a loop body with a container fan-out multiplies it. The scope
   tests the callee, but the growth is in a caller block (a loop body).
   An acyclic callee that such a loop body calls is inside the scope.
2. The cover defect does not cause the growth, and the obvious shape
   restriction (MAY-tail replies only, the only shape that OWASP needs)
   does not prevent it.
3. The rule is exact for the NORMAL facts of the run where it acts (with
   cover item 3), but it is not a subsumption of the demand. It removes
   demand rows. With fewer rows, C5 (which selects and cuts for each row
   and publishes the union) can publish fewer coarse cuts, and the finer
   leaves that a coarse cut held become visible. The lost depth-2 FLOW
   leaves fit this reading; which H6 rows are missing is not traced
   (INFERENCE). The widening is bounded (one more field level), but it
   costs 3-4 times the run-7 time on Conductor.

So a restriction by the shape of the reply does not give a rule without
negative consequences: the consequence is in the demand that the
dropped fact would make, not in the fact. Open (§7 item 4).

**Gate alone.** Module identical, 2 end earlier; jvm 6 of 6; rule suite
identical; OWASP identical, 151.7 s, residual 705. Alone the effect is
small; with §5.2 and §5.5 it closes the `doSomething` families.

**Cost.** Per NORMAL MUST leaf of a saved replay result (record), per
DEMAND reply applied to a NORMAL offer (check), one scope query per
covered reply. OWASP 38,929 cover leaves, 29,429 checks, 167 drops;
Stirling-PDF 42,054 checks, 12 drops; Conductor 356,562 checks, 2 drops.

### 5.5 An EXACT cleaner does not apply to a MUST leaf

Flag `-Dorg.opentaint.bidi.mustIgnoresExactCleaner=true`. Decision of 21
November.

**Definition.** A cleaner is `κ = (β.p, reach, M)`: a position, a reach
(EXACT, BELOW or AT_AND_BELOW) and the marks that it removes. A TAINT
leaf `λ` with the base `β` and the path `q` is in the PART position of
`κ` when `q` is a prefix of `p` and the point `β.p` is in `R(λ)`.

```text
native PART (EXACT reach, MUST leaf):
              the leaf λ loses the marks M; a leaf q.MUST/E with the marks M is
              added on layer D (the "survivor"): the whole region, the cleaned
              point included, is demoted to D (ap/Clean.kt:185-202)
rule:         if reach(κ) = EXACT and τ(λ) = MUST:  λ stays unchanged
              (same layer, marks, exclusion and protection; hook at :186)
```

All other cases keep the native cut: `$` leaves, `MAY` and `*` leaves,
FLOW facts, BELOW and AT_AND_BELOW cleaners. The rule applies in both
directions and in every run. The reference model follows
(`ap/Reference.kt`, `concPart`).

**Why the native form makes demand.** For `p = q·p1…pn` the exact rest is
`q.MUST{p1} ∪ … ∪ (q.p1…pn)·Σ⁺`. The last piece (every strict descendant
of the point) has no NORMAL form: `E` holds only first accessors, and a
MUST leaf always covers its own position. So native demotes the whole
region. No K and no refinement can make it NORMAL.

**Trade.** The cleaned point stays tainted inside a MUST region. This can
add a confirmed report where native has a provisional one.

**Example (OWASP `Thing2#doSomething`).** `return new
StringBuilder(i).toString()`. The propagator `$RES = (Object
$*OBJ).toString()` (`rules/ruleset/java/lib/generic/path-traversal-sinks.yaml:16`)
resets the mark at `ret` with reach EXACT. The input is `ret.MUST/T,N`.
Native gives the survivor `ret.MUST/T,D`; the rule keeps `ret.MUST/T,N`.
The same maker makes the DEMAND witness at 151 of the 164 open acyclic
OWASP `doPost` roots.

**Gate alone.** Module: 4 report changes, one analysis that ends earlier
with the same report (`DemandLinkTest`), and 12 unit tests that state the
native survivor (list: [acyclic-group-a-implementation.md](acyclic-group-a-implementation.md) §4.5). The report changes:
`UniformRootCleanerTerminationTest` (1 new confirmed result, 1
provisional → confirmed), `DescendantCleanerTerminationTest` (provisional
→ confirmed), `AcyclicTerminationBaselineTest.protectedGlobalCutGrowth`
(provisional → confirmed). These fixtures state the expected answer in
their own control cases. They are signed off (§1). jvm: 6 of 6
analyses identical, 2 cleaner-table tests fail. Rule suite identical, 20
end earlier. OWASP identical, 128.1 s, residual 24: the largest single
effect.

**Cost.** Per EXACT cleaner application on a MUST leaf at PART. OWASP
2,005 forward NORMAL applications and 2,662 in run-1; Stirling-PDF 41;
Conductor 106.

### 5.6 The relative C5 cap: no rule

Revision 1 had `acC5Exact` (no relative cap on NORMAL selections of
acyclic methods) and C5B (the same at acyclic block exits). This revision
withdraws both. Evidence: branch `proto/c5-passenger-20261123`, report
`docs/reports/c5-passenger-20261123.md`.

**Question.** The cap `min(K, FL(Dp)+1)` also cuts in acyclic code, and
the cut does not read K. Does the cap keep acyclic demand alive by
itself?

**Terms.** A *cut row* is a handoff row that a relative cut at C5 makes.
An *anchor row* is a row of another maker class in the same owner: an
inside read or other raw DEMAND, a DEMAND start, or an ND summary.

**Lemma (a cut does not renew itself at its own depth).** Line numbers in
this lemma refer to commit `e83267031` (branch
`proto/stirling-ac-20261121`, the base of the evidence branch). Let a
forward run with the limit `K` publish the cut piece
`q = (a → b.MAY, D)` with `FL(b) = FL(Dp)+1`. A relative cut happens only
when `FL(Dp)+1 < K`.

1. The handoff projects `q` to the row `(entry = b.MAY, exit = a)`
   (`driver/HandoffCompactor.kt:139-153`).
2. The backward run starts every initial under the entry `b.MAY` at a
   depth of at least `FL(b)` (`ap/RestrictedInitialPolicy.kt:30-63`): an
   actual at `b` starts at `b`; an actual below `b` starts one counted
   field below `b`; a MAY or MUST actual above `b` starts at `b`; a `*`
   or `$` actual above `b` gives no start.
3. Only DEMAND, ND and ZERO backward summaries are handed off
   (`ap/Demand.kt:136-140`). A handed-off backward summary of a start `s`
   gets the exit `s`. The next forward run has the limit `K' ≥ K+2`
   (`K = max(1, i-1)` for run `i`), and its C5 budget for that exit is
   `min(K', FL(s)+1) ≥ FL(Dp)+2` (`store/DemandStore.kt:300`).
4. After run-2, C2 and C5 read only the rows of the owner itself
   (`store/DemandStore.kt:187, :274`; `driver/HandOff.kt:228`). For a
   ZERO actual or premise a block view also reads the rows of the
   normal-interface scope (`engine/BlockBoundaryDemandView.kt:40-44,
   :62-63`). DATA cut rows are not affected.

So every pair that comes from `q` cuts deeper than `q`. A cut at the
same depth in a later run needs a pair from an anchor row. Along a chain
of cut rows the cut depth grows strictly. One code path can make a
descendant row shallower: C5 publishes a `*` conclusion above the exit
whole (`ap/Reference.kt:253`). No measured lineage shows it.

**The fix belongs at the maker, not at the rows.** In
`AcyclicTerminationBaselineTest.protectedGlobalCutGrowth` a one-time
removal of the anchor rows does not close the owner. The conclusion
`b.MAY` of a cut row is a C2 key one field deeper, and the
K-independent makers (inside read, DEMAND STAR start) act on every start
that C2 admits, at every depth. So the family moves one level down and
lives until run-101. A rule that removes the maker acts at every level;
a one-time removal of rows does not.

**Measurement.** AO-C5 = §5.1-§5.5; AO = AO-C5 + `acC5Exact`. Native
stop, no canonical order, no W. Reports identical in every arm.

| Project, last forward barriers | AO-C5 rows / owners | AO rows / owners | What `acC5Exact` removes |
| --- | --- | --- | --- |
| OWASP, H7-H11 | 6 / 1 | 2 / 1 | 4 cut rows in `BenchmarkTest01874#doSomething` (anchor: inside read) |
| Stirling-PDF, H9-H11 | 5 / 3 | 5 / 3 | no forward row; 4 backward cut rows of `saveUser` |
| Conductor, H7 | 16 / 6 | 11 / 6 | 5 cut rows in an `Optional#map` lambda (anchor: inside read) |
| Module suite | 18 analyses / 47 rows | 18 / 47 | nothing |
| Rule suite | 1 / 8 | 1 / 8 | nothing |

- The set of open acyclic owners is the same with and without the rule.
  The rule closes no owner on any project.
- The lineage diagnostic (`c5Lineage`) gives every late cut row an anchor
  root. No cut row has only cut rows as roots.
- A one-time removal of the anchor rows removes the cut rows for good on
  all three projects (OWASP 6 → 0). A one-time removal of the cut rows
  keeps the anchors, and the cut rows come back at the next forward
  barrier.
- C5B has nothing to do: `decodeMimeHeader` block 1 has no row from H5,
  because RX removes its anchor.
- Time: no difference beyond the spread (OWASP 110.7-112.8 s against
  110.6-112.7 s; Stirling-PDF 55.7-56.0 s against 56.6-56.7 s).

**Alternatives.**

| Alternative | Rule | Exact? | Cut events changed (OWASP / Stirling-PDF / Conductor) | Result | Verdict |
| --- | --- | --- | --- | --- | --- |
| (A) `acC5Exact` | no cap on NORMAL selections of acyclic methods | yes | 59 / 101 / 198 | removes passengers only; a call-cone property decides a local C5 step; it does not touch cuts of DEMAND selections | withdrawn |
| (B) cap only at cycle points | keep the cap only at loop repeat ports and at roots of recursive methods | per publication, as (A) | 97 / 7,683 / 101,500 | same report and residual; Stirling-PDF driver +37 %; the cap is not a widening, so this placement gives no termination property | rejected |
| (C) a finer row covers the coarser cut | a coarser row does not publish its cut when another row of the same C5 query keeps every cut leaf whole | no: the MAY piece reaches sinks that the exact leaf does not reach, so it can remove provisional results; the restriction spec §5.4 rejects this cross-layer dominance | — | OWASP residual stays 6; driver +15 % (OWASP), +35 % (Stirling-PDF) | rejected |
| (D) no rule | native C5 everywhere | native | 0 | passenger rows stay only while their anchors stay | **selected** |

**Decision (24 November): (D).** The relative cap is a passenger: in acyclic
code its rows exist only while an anchor maker acts in the same owner.
(D) is "one rule out" (design-guide rule 7) and the trivial alternative of
rule 10. Without (A) the residual stays an honest test of a maker fix: a
fix that leaves a maker active at a deeper level shows up as cut rows
that come back.

The robustness rule (§1) excludes (A) on its own. Its premise "an acyclic
method has a bounded depth" is a property of the code and of the outer
inputs. `ExclusiveJoinTaskMapper#getMappedTasks` is acyclic by §3, but
the alias analysis gives it deep facts (§7 item 3). There the cap
publishes one more field per round (budget 3 at H5, 4 at H7) while the
body reaches K. (A) would lift the cap for its NORMAL selections.

**Withdrawal condition of (D).** Look at the cap again if (1) an acyclic
owner has a cut row whose parents are cut rows only, at the same depth,
at two consecutive forward barriers (possible only through
`ap/Reference.kt:253`), or (2) an acyclic owner reaches zero forward rows
with (A) and not with (D) under the same anchor rules.

**Other maker found here.** On Conductor,
`ExclusiveJoinTaskMapper#getMappedTasks` is acyclic by §3, but its output
is cut at K in every run up to run-7:
`ret.Iterable#Element.TaskModel#inputData.Map#MapValue…` repeats.
Neither (A) nor (D) acts on it: it is a cut of a DEMAND selection. The
cause is an alias self cycle with a bound of 9 fields (§7 item 3).

### 5.7 Owner cover (proposed 24 November)

Flag `-Dorg.opentaint.bidi.dtOwnerCover=true`. Branch
`proto/dt-owner-cover-20261124`, report
`docs/reports/dt-owner-cover-20261124.md`. Proposal of 24 November: drop
`DemandTarget(id)` at the owners that have a NormalTarget for `id`, so that
a caller that does not get the NormalTarget keeps its DemandTarget.

**Definition.** At the barrier of a restricted forward run `i` (run-3
onward, `driver/HandOff.kt` `toCompacted`):

- `NT_i(o)` = the NormalTargets of owner `o` (a method, or a block scope
  of a method): saved, and made in run `i`.
- `R_i` = the outgoing `P → DemandTarget(id)` rows. The witness tags each
  DemandTarget with its id (the RX tag, §5.3).
- `E_i` = the relay edges of run `i` between pairs `(owner, id)`: callee →
  caller at a call relay (`engine/RunMethodCallServices.kt` `applyTarget`),
  child block → parent scope at a block lift
  (`engine/MethodBlockRuntime.kt` `onTerminal`).

```text
P ⊨ Q            ⟺  Q = ZERO, or members(Q) ⊆ members(P)
covered(o,P,id)  ⟺  ∃ Q: (Q → NormalTarget(id)) ∈ NT_i(o) ∧ P ⊨ Q
kept(o,id)       ⟺  some row (o,P,id) ∈ R_i is not covered,
                     or ∃ (o,id) → (o',id) ∈ E_i with kept(o',id)        (least fixed point)
drop (o,P,id)    ⟺  covered(o,P,id) ∧ no (o,id) → (o',id) ∈ E_i with kept(o',id)
drop seeds of id ⟺  a DemandTarget(id) row was dropped and none stays (predicate-sink seeds stay)
```

In-run relays keep their premises and layers, so a caller that does not
get the NormalTarget (another premise, or a DEMAND binding) still gets the
DemandTarget during the run and keeps its own row. But the tag splits
DemandTarget rows, relays and ND joins per report id where native merges
them (target rows and join keys contain the target); two module tests that
assert the merge fail, as under RX. The implication `P ⊨ Q` uses only the
forms that need no pattern reasoning. The lineage is per `(owner, id)`,
not per row, and a call relay records its edge per member binding, before
the ND join and before `acceptsTarget`; so the lineage has extra edges and
keeps more rows than an exact per-row lineage. The edge store is keyed by
the run index only (another analysis in the same JVM can leave edges; this
also only keeps rows).

**Why the lineage (fixture M3, `DecidedStopAttackTest`).** Callee `g` has
`ND[a0 & a1] → NormalTarget(B)` from two split call sites. A deep call
binds `a0` on DEMAND. Its DEMAND arm at `g` has the same premise. Without
the lineage the rule keeps the root's `DemandTarget(B)` (B is not
confirmed) and the seeds of B, but it drops `g`'s own row, and B is lost
(confirmed `{A}` instead of `{A, B}`): the backward run needs `g`'s row to
compute `a1` at the deep call. With the lineage `g`'s row stays (it relayed
into the root's kept row) and M3 keeps B. This is the counterexample of the
earlier ND cover (§5.3 "Why not a wider cover"); the barrier form alone
does not remove it.

**Exactness argument.** Take a dropped row `(o, P, id)`. (1) At `o`, the
refinement that the row asks for can only make `P' → NormalTarget(id)`
with `P' ⊨ P ⊨ Q`, which `Q → NormalTarget(id)` already implies. (2) Above
`o`, every relay of `DemandTarget(id)` from `o` in this run went into an
owner whose rows are all dropped, up to owners with no relay. A caller that
binds the premise on DEMAND does not get the NormalTarget (it does not relay
into a DEMAND binding, `engine/RunMethodCallServices.kt:510`), so it keeps
its row, and the lineage keeps the path below it. Assumption, not shown:
that caller's row is accepted (`acceptsTarget`) and its ND join completes
in the run; otherwise its edge exists but it is not kept, and the callee
row is dropped. (3) Every other id keeps its own witness, DemandTarget and
seed, if the analysis is monotone in K (assumed; M4 is the only test): the
rule needs §5.1, as X does (without G6 it removes finding B of M4).

The argument covers targets and reports only. Refinement also makes
NORMAL facts and records that are not targets, for example a second route
to a sink that is already confirmed. Four module fixtures were written as
counterexamples to "a report id proves that every route is served". In all
of them the report does not change, and the second route is not served:

| Fixture | Native end | G6 + X (and AO-C5) | G6 + owner cover |
| --- | --- | --- | --- |
| `DistinctMarkOriginServiceTest` (acyclic, deep chain `x.f.f.f.f`) | 3-5 | 1 | 3 |
| `UniformCoverageOriginAuditTest` (acyclic) | 3-5 | 1 | 3 |
| `RecursiveWrapperTerminationTest` (recursion) | 9, 101 | 7 | 5 |
| `LoopMarkOriginServiceTest` (loop, two marking origins) | 13, 17 | 13, 17 (served) | 5 (not served) |

So X, an accepted rule, already acts like the rejected report-only
retirement on the first three; owner cover adds the loop fixture, where the
renewing rows are a block row and its lift into the root (X and RX do not
act there). For `LoopMarkOriginServiceTest` the missing route is VERIFIED
with a print of the test's `deepBefore` check (native and G6 + X: served;
G6 + owner cover: not served; the test asserts the end run first). On the
three projects the SARIF code flows stay identical. Not covered either:
callers that are not analysed in run `i` are not in `E_i`.

**Example (OWASP).** At the run-3 barrier the rule drops all 1,150 outgoing
DemandTarget rows (502 with a ZERO premise); 268 report ids lose all their
rows. Run 5 has no forward demand row, and the analysis ends by itself at
run 5 (`NO_DEMAND_EDGE`) with 2,633 / 0 and identical code flows. Native
ends at `RUN_LIMIT` 11, AO-C5 too (residual 6).

**Gate (single launch per item, 24 November).** Arms: G6 + owner cover
(the rule with its prerequisite), and AO-C5 with owner cover in place of
MUST-cover (G6, X, RX, cleaner rule, owner cover).

| | Native | AO-C5 | G6 + owner cover | AO-C5 with owner cover, no MUST-cover |
| --- | --- | --- | --- | --- |
| Module suite (342 analyses on this branch) | 30 / 81 open | 18 / 47 (291 analyses) | 308 identical, 29 end earlier, 3 other end changes (below); report changes: M4 ×2 (decided G6); 19 / 54 open | 301 identical (+16 with suppressions), 33 end earlier, 2 other end changes; report changes: the 4 signed-off cleaner fixtures, M4 ×2; 16 / 45 open |
| Jvm suite | 6 | 6 identical; 2 cleaner assertions fail | 6 identical | 6 identical; the same 2 cleaner assertions fail |
| Rule suite (585) | 2 / 9 open | 1 / 8 | 0 outcome changes, 582 identical, 3 end earlier; 0 / 0 open | 0 outcome changes, 562 identical, 23 end earlier; 0 / 0 open |
| OWASP | `RUN_LIMIT` 11, 150-153 s, residual 711-735 | `RUN_LIMIT` 11, 112.8 s, residual 6 | **`NO_DEMAND_EDGE` 5**, identical, 120.6 s, residual 0 | **`NO_DEMAND_EDGE` 5**, identical, 108.1 s, residual 0 |
| Stirling-PDF | run-11 stall (2,704 s), 32 / 2 | `RUN_LIMIT` 11, 55.7 s, residual 5 | `RUN_LIMIT` 11, 32 / 2 identical, 56.6 s, residual 5 | `RUN_LIMIT` 11, identical, 54.2 s, residual 5 |
| Conductor | timeout run-8, 7 / 0, H7 at 666 s (84,944 rows), residual 21 | identical, H7 at 600 s (80,815), residual 16 | identical, H7 at 593 s (78,716), residual 15 | identical, H7 at 586 s (79,176), residual 15 |

Every project launch has identical confirmed and provisional results and
identical code flows. The module-suite report changes are the decided
exceptions only. Other end changes: two module analyses end `ABNORMAL` at
run 5 (the "report-only retirement" hook of `LoopMarkOriginServiceTest`
looks up the root analyzer in run 5, and with the rule the root is not
analysed there: a test-hook artifact, not an engine failure), and one
analysis that ends `ABNORMAL` natively at run 22 ends `ABNORMAL` at run 21.
Stirling-PDF times are under host load in every arm (mean load 5.9-7.3,
the AO-C5 reference 7.3); during the G6 + owner cover launch an unlocked
unit-test run of this work also overlapped.

**Cost.** Per forward barrier: an index of the saved and current
NormalTargets, two passes over the outgoing DemandTarget rows, each with a
cover test (largest: Conductor 5,042 rows), and a reverse closure over the
relay edges (largest: Stirling-PDF 2,709). Per member binding of a tagged
relay: two hash operations. No seed was dropped in any launch, also where
every row of an id was dropped (OWASP 268 ids, Stirling-PDF 12): the seed
branch never acted. Why (for example predicate-sink seeds, which the rule
keeps) is not measured.

**Consequence (not decided).** Without X, RX, MUST-cover and the cleaner
rule, G6 + owner cover matches or improves the residual of AO-C5 on the
three projects and the rule suite: OWASP and the rule suite end by
themselves, and the cleaner fixtures do not change. It does not improve the
module-suite residual (19 / 54 against 18 / 47: without the cleaner rule
the cleaner fixtures stay open) or the OWASP time (120.6 s against 112.8 s,
one launch each). The row that X suppresses is a case of owner cover (a
ZERO cover at the witness owner), but X also acts in run-1 and during the
run, where it stops the relay and the seed: the OWASP forward residual is
7,086 without X against 4,780 with it at run-1, and 95 against 56 at
run-3. RX is not fully included: RX also stops the
relay above the covered caller, while owner cover lets it continue and
keeps the rows of owners above that have no covering NormalTarget; on the
three projects this made no difference to the residual. With owner cover
the OWASP `doSomething` families close without MUST-cover and its acyclic
scope (which DemandTarget rows did it there is not traced per owner). Open
decision: accept the loop-route
behaviour above, and replace X, RX, MUST-cover and the cleaner rule by
owner cover.

**Route condition (24 November; the form above was rejected).** Decision
of 24 November: the rule must also keep the demand that serves a second
route to a confirmed sink. Branch `proto/dt-owner-route-20261124`, report
`docs/reports/dt-owner-route-20261124.md`. New gate check, the sink-route
census (`-Dorg.opentaint.bidi.sinkRouteCensus=true`): the set of NORMAL
leaves that reach each sink in the forward runs, as
`rule@method:statement|leaf`. Two arms serve the same NORMAL routes when
their sets are equal.

Definition added to the drop condition. During the run the witness records,
per `(owner, id, input premise)`, the NORMAL leaves that reach the sink, and
per DemandTarget row the DEMAND leaves of its arm. A witness row may be
dropped only when each of its DEMAND leaves would be absorbed by a NORMAL
leaf of the same input premise at the same sink if it became NORMAL
(in-layer subsumption, `ap/Reference.kt:586`; a MAY or STAR leaf never). An
owner with an uncovered route, and each owner it relayed `DemandTarget(id)`
into, keeps its rows. A first version with region cover (`covers`) still
lost the second EXACT track of `UniformCoverageOriginAuditTest` under a
uniform NORMAL MUST. The tag is now made only in restricted runs: in run-1
it changed NORMAL routes of three static fixtures.

Results (VERIFIED, single launch per item; the projects and the rule suite
ran at `f2032b5c9`, before the run-1 tag change; the module suite at
`29e5997f4`, after it):

| | Native | G6 + owner cover with the route condition |
| --- | --- | --- |
| Route fixtures (45 analyses) | reference | equal to G6 alone in end, report and routes |
| Module suite, routes per class (identity hashes removed) | reference | equal to G6 except 2 classes: `StaticCatalogIterationTest` loses `arg(0).MUST/T E{Box#g}` (the analysis ends at run 3, so a tag effect in run 3, not a dropped row); `AcyclicTerminationBaselineTest` gains `var(2).Box#f.Box#f.MUST/T` in a 101-run analysis |
| Module suite, open | 30 / 79 | 28 / 79 |
| Rule suite | 2 / 9 open | identical to native in every analysis, including routes |
| OWASP | `RUN_LIMIT` 11, 150 s, residual 711-735, 6,325 routes | `RUN_LIMIT` 11, 150.3 s, residual 585, reports and code flows identical; 19 routes lost at 5 path-traversal sinks (`BenchmarkTest00452`, `02197`-`02200`) |
| Stirling-PDF | stall in run-11 | stall in run-11 (timeout at 3,000 s, 32 / 0) |
| Conductor | timeout run-8, 7 / 0 | identical, routes equal (14), H7 84,410 rows, residual 20 |

The 19 lost OWASP routes are deeper EXACT leaves (for example
`<this>.File#path.String#bytes.$`) under a NORMAL `<this>.MUST` that the
arm keeps. Native finds them in later runs, when K grows and C2 starts
deeper premises. Mechanism (INFERENCE): a DemandTarget row keeps its owner
analysed in later runs, and every later run at a larger K makes finer
NORMAL facts for all flows to that sink, not only for the DEMAND route of
the row. A DEMAND MUST leaf that a NORMAL MUST absorbs at the current K is
therefore not finished. For comparison, AO-C5 against native on OWASP:
1,391 routes only in native, 161 only in AO-C5 (reports and code flows
identical); X already loses the second routes of three fixtures (above).

Conclusions:

1. The gains of the first form came from stopping route refinement. With
   the route condition the rule keeps 983 of the 1,150 OWASP rows at run-3
   and has almost no effect anywhere.
2. Under a leaf-level route gate, removing the last demand of an owner is
   exact only when the owner's analysis under that premise no longer
   depends on K: no global cut, no start or C5 output bounded by K in the
   run (K-saturation). In acyclic code that holds once K is larger than
   the depth bound, which is the premise of requirement AC. The engine
   does not track this per owner and premise today; not built.
3. Under the same gate X, the RX tag, MUST-cover and the cleaner rule also
   change routes (AO-C5: 1,552 route differences on OWASP).

Open decisions: (a) which routes the gate must keep: every NORMAL leaf at a
sink (as measured), NORMAL leaves up to region cover at the same sink, or
code flows only; (b) whether the route census becomes a gate check for
every rule; (c) whether to build the K-saturation condition or to withdraw
owner cover.

## 6. Combined result

AO-C5 = §5.1-§5.5 on the native runtime. Branch
`proto/acyclic-only-20261123` (`3693de8a1`, `f33ff8538`), report
`docs/reports/acyclic-only-20261123.md`. Data:
`/drive-testcomp/opentaint-go-rules/termination-next-20261119/acyclic-only/`.
Every arm, native included, runs with the residual diagnostic. It costs
17.4-17.7 s per OWASP launch natively and 13.7-14.1 s in AO-C5.

| | Native | AO-C5 |
| --- | --- | --- |
| Module suite (314 analyses) | reference; 30 / 81 open | 288 identical, 22 end earlier, 4 report changes (§5.5); 18 / 47 open |
| Jvm suite (6 analyses) | reference | 6 identical |
| Rule suite (585 analyses, 786 enabled cases) | reference; 2 / 9 open | 563 identical, 22 end earlier, 0 report changes; 1 / 8 open |
| OWASP, 3 interleaved launches each | `RUN_LIMIT` 11; 2,633 / 0; driver 150.2-153.1 s; residual 711-735 | `RUN_LIMIT` 11; identical SARIF and code flows; driver 110.7-112.8 s; residual 6 |
| Stirling-PDF, 2 launches each | run-11 stalls: 2 of 2 time out at 3,000 s (32 / 0); a third launch with 7,200 s completes after 2,704 s (32 / 2); residual 49 | 2 of 2 `RUN_LIMIT` 11 after 55.7-56.0 s; 32 / 2, identical to the completed native run; residual 5 |
| Conductor, 1 launch each | timeout in run-8; 7 / 0; H7 at 666 s; residual 21 | timeout in run-8; identical; H7 at 600 s; residual 16 |

- Memory: the largest heap after a GC is not worse (OWASP 6,771-7,140 MiB
  against 6,976-7,254 MiB; Stirling-PDF 6,837 against 7,314-7,347 MiB).
  Peak RSS saturates near the 8 GiB heap in every launch, and Conductor
  is at the heap limit in every arm, so a memory regression there is not
  visible.
- Stirling-PDF: against the two timed-out native launches, AO-C5 has the
  two provisional results `UserController.java:753` and `:768` more.
  Native publishes them when its run-11 completes. Which rule removes the
  run-11 stall is not measured (no single-rule arm on Stirling-PDF).
- Residual per forward barrier, OWASP: native `3:696 5:697-705
  7-11:711-735`; AO-C5 `3:57 5:2 7-11:6`.

Open acyclic owners with AO-C5:

| Project | Owner (rows) | Maker |
| --- | --- | --- |
| OWASP | `BenchmarkTest01874#doSomething` (2 + 4) | inside read and its cut passengers |
| Stirling-PDF | `UserService#saveUser` (2) | inside read (§7 item 1) |
| Stirling-PDF | `AuthController#login` (1) and its entry point (2) | DEMAND STAR start from a backward MAY row |
| Conductor | `Optional#map` lambda of `SubWorkflowTaskMapper` (6) | inside read and its cut passengers |
| Conductor | `ExclusiveJoinTaskMapper#getMappedTasks` (1) | alias self cycle (§7 item 3) |
| Conductor | `DummyPayloadStorage#download`, `ExternalPayloadStorageUtils#downloadPayload`, `ScriptEvaluator#getSource` (5 Target rows); `StartWorkflow#getRequest` block 1 (4) | not traced |

## 7. What remains

1. **Inside reads (anchor).** The `new String(byte[])` model edge on the
   coarse premise `arg(1).String#bytes.*` gives a DEMAND reply `ret.MAY`
   that also reaches exact actuals `String#bytes.$`. Two rules removed it
   at the source ("start the finer premise in the same run", "mark the
   reply unrefinable"). Both remove the two native provisional
   stored-XSS results `UserController.java:753` and `:768` on
   Stirling-PDF. These results exist only because the reply's demand rows
   in `UserService#saveUser` make a coarse backward row
   (`REPO.MAY/XSS => ZERO`) that restarts the controllers in every later
   run. For this maker, AC and identical provisional output cannot both
   hold. Decision (24 November): keep the provisional results. So the
   `saveUser` rows are an accepted exception to AC. A future rule for the
   inside read must keep these two results; the two tested rules stay
   rejected. Carrying reached sets across runs is not selected (on OWASP
   it would add about 500 provisional results).
2. **DEMAND STAR start (anchor).** C2 makes a STAR start with a concrete
   mark, which is DEMAND by itself, one field below an ANY entry. The ANY
   entry comes from a backward MAY row (reversed MAY rule edge or
   any-field sink seed; Stirling-PDF `AuthController#login`) or from an
   ANY demand over a deeper NORMAL actual (10 module fixtures). The exact
   start that removes it refines deeper than the demand requests, and it
   was rejected (§8). No exact cover is known.
3. **Alias self cycles (analyzer artifact).** Evidence: branch
   `proto/acyclic-growth-20261124`, report
   `docs/reports/acyclic-growth-20261124.md`.
   - Cause in `ExclusiveJoinTaskMapper#getMappedTasks` (Conductor). The
     method makes a new `HashMap` and calls `put` twice; no loop, no
     recursion, no heap cycle. Two defects of the alias call model put
     the map and its value `map.MV` in one alias group: (a) it reads the
     row `javax.script.Bindings#put: arg(1) → this`, which rule storage
     pushes up to `Map#put` with the condition `this is Bindings`, but
     without the condition (`JIRLocalAliasAnalysis.kt:75-90`); (b) it
     reads every copy as a reference assignment and merges both sides
     (`DSUAliasAnalysis.kt:183-190`). At the next call the ALIASES stage
     (`JIRCallPlanBuilder.kt:353-370`) writes the callee `this` into
     `map.MV^1..6` (the alias chain stops at 6 levels). So the premise
     comes out 9 fields deep, and the output is cut at K while `K < 9`.
     Native shows the same cuts. The rules involved have no `[any]`, so
     the case is inside the assumption of §1. The depth is bounded; by
     inference the cuts end near forward run-15.
   - Other cases: 12.6 % of OWASP call plans have a self alias (4.9 %
     Stirling-PDF, 3.5 % Conductor). Every acyclic owner with a global cut
     after run-4 on the three projects has one: `getMappedTasks` and
     `DynamicTaskMapper#getDynamicTaskName` (Conductor), and 7
     Stirling-PDF owners (with a repeated `Optional#Element`,
     `Map#MapKey`, `Matcher#input` or `Put#MapValue`). All of them end by
     run-9, except `getMappedTasks`, which is still cut at H7, the last
     barrier before the Conductor timeout. The module-suite cases are deep chains that the fixtures
     write themselves (the bound holds there).
   - Source fix, not prototyped: the alias call model evaluates the row
     condition at the call site, as the taint call plan does, and it
     reads only rows that keep the reference (the parsed
     `taintCopyOnly` marker is not used today; `append` rows are not
     marked). A narrow form (drop copies into a bare `this` or argument)
     keeps the reports on OWASP, Stirling-PDF and both suites, but
     Conductor runs out of memory in run-2 in 2 of 2 launches. Not
     traced.
   - Consumer-side prototype `aliasNoSelfEdge` (R4): the ALIASES stage
     writes no call position below the caller local that it is bound to.
     Reports identical to AO-C5 on OWASP (3), Stirling-PDF (2), Conductor
     (2), the rule suite and the jvm suite; time and memory not worse;
     `getMappedTasks` has no row from H5. It is not exact for a real heap
     cycle (for example a parent back-pointer: `x == x.parent.child`):
     there it drops facts that native keeps for 6 levels. Not selected.
   - Under the robustness rule (§1) no fix of the alias analysis is
     needed against fact explosion: the relative cap already makes the
     deep facts wait for demand, and the case costs no measurable time.
     The source fix and R4 are a precision item of the alias analysis,
     outside AC.
   - Open: natural termination does not have the same robustness. The
     deepening row stops only at the alias chain limit, a constant of the
     alias analysis. An alias input with an unbounded self cycle (real or
     not) would deepen the row by one field per round for ever: no
     explosion, but no `NO_DEMAND_EDGE`, and no `FIXED_POINT` (the row
     changes, and the body cut reads K). Candidate: treat a self cycle
     that the alias analysis reports like a program cycle. The cycle fold
     W (main proposal §6.1) then also acts where the ALIASES stage writes
     through a self alias, the row becomes stable, and the owner leaves
     the AC scope. Not prototyped.
4. **The MUST-cover scope reads a call-cone property** (§5.4). This is
   the weak point that withdrew `acC5Exact`. The trace of 24 November
   (`proto/must-cover-shape-20261124`) shows that the scope is a proxy.
   The unscoped growth is a widening of DEMAND summaries in the loop body
   of `ParametersUtils#replace` / `replaceList` one run after the demand
   rows change. Neither the cover fix nor a MAY-only restriction prevents
   it. On OWASP the rule is needed only for three `doSomething` helpers
   (AO-C5 without it: residual 24 instead of 6, reports identical).
   Measured instead of H-global: owner cover (§5.7) closes them without
   MUST-cover (OWASP residual 0, natural end at run 5). To trace the
   widening itself: a backward census of H6 in `replace` block 2.
5. **Not traced:** the Conductor Target rows and `StartWorkflow#getRequest`
   block 1 (§6); rule case 349 (8 Target rows in a block of
   `UnsafeFileUploadServlet#doPost` that no loop precedes).
6. **Module fixtures.** Rows from an intrinsic MAY rule (outside the
   assumption) stay.

## 8. Rejected after test

| Rule | Why |
| --- | --- |
| `acC5Exact`: no relative C5 cap in acyclic methods (revision 1 §3.6) | Removes passengers only; closes no owner on any project (§5.6) |
| C5B: no relative cap at acyclic block exits (revision 1 §3.7) | RX removes its anchor; nothing is left to act on (§5.6) |
| Relative cap only at cycle points | Not a widening, so no termination property; Stirling-PDF driver +37 % (§5.6) |
| A finer row covers the cut of a coarser row | Can remove provisional results; the restriction spec §5.4 rejects it; driver +15-35 % (§5.6) |
| Offer closure: no start for a DEMAND offer that the callee's record covers | Loses `delayed U sink`: the callee row is also the C2 admission key for later refined offers |
| Exact start: start a deep actual at its full depth | Refines deeper than requested; facts in affected callees +20-60 % |
| Excluded-point exclusion member ε for cleaned MUST regions | Replaced by §5.5, which needs no new representation |
| Do not hand off a complete row already served | Loses findings: with a larger K the same row is a different input |
| Persist backward ZERO rows as admission rules | Loses M3: the backward run no longer reopens the seed path |
| G6 guard (no stop while boxed drops happen) | Conductor drops in every run, so X never acts there |
| G6 keep form (keep MAY-tail marks at boxed levels) | Not selected; the drop form matches the policy's intent |
| Inside-read rule; unrefinable MAY (option A) | Remove two native provisional results on Stirling-PDF (§7 item 1) |
| DemandTarget relay with a call-site seed (ND cover, RELAY) | Exact, but 3 min against 3.4 s in one forward run |
| ND cover at the witness (premise subset) | Loses `B@g:1` in fixture M3 (§5.3) |

## 9. Semantic scope

Changed: the primitive-tracking mark policy at boxed levels (§5.1);
DemandTarget emission and seed capture at a forward sink witness whose
owner has a complete ZERO target for the same report (§5.2); the relay of
a tagged DemandTarget into such an owner, and a report identity on the
DemandTarget (§5.3); the reply set at a call to an acyclic callee
(§5.4); an EXACT cleaner on a MUST leaf (§5.5).

Unchanged: C2, C5 and the relative cap, the stop rules, the handoff
projection and compaction, field transfer outside these sites, run-1 and
run-2 static views, the field-limit schedule, the report rules.

## 10. Implementation and gate plan

1. Land the rules behind their flags in this order: §5.1, §5.2, §5.3,
   §5.4, §5.5. §5.2 and §5.3 need §5.1. §5.4 needs the scope of §3.
   Before §5.4 lands, fix its cover test (item 3 of the cover in §2) and
   gate it again.
2. Change the unit expectations that check the old representation: the
   tagged DemandTarget of §5.3, the cleaner tables of §5.5, the G6 tests
   of §5.1. Review the failing end-run and internal-row assertions one by
   one.
3. Gate each rule alone and the combination against native, as in §6:
   module suite, jvm suite, rule suite, OWASP 3 interleaved launches per
   arm, Stirling-PDF 2, Conductor 1. Add single-rule arms on
   Stirling-PDF to find the rule that removes the run-11 stall. Report
   the forward AC residual in rows and in owners.
4. Measure the time of AO-C5 without the residual diagnostic.
5. Then measure AO-C5 on the stack of the main proposal (canonical
   order, `FIXED_POINT`, W, LG, CA).

## 11. Proof scope, checklist and blind spots

```text
[x] Failure class and real trace: §4, the example of each rule
[x] Ablation on the real case: per maker (revision 1 reports); anchor and cut ablation (§5.6)
[~] Native prototype, 3 launches: OWASP 3 per combined arm; Stirling-PDF 2; Conductor 1; single rules 1 (OWASP)
[x] Execution site and volume of each new operation: §5
[x] Selected semantic scope: §9
[ ] Proof scope: no rule has a proof
[x] Withdrawal condition: a changed report withdraws the rule; §5.6 for the cap
```

- No rule has a proof. The exactness arguments are code readings,
  checked by native fixtures and gates. The C5 lemma (§5.6) has one
  unexercised exception (`ap/Reference.kt:253`).
- An adversarial review of the definitions against the code found three
  errors in the first draft. They are corrected here: the cover test of
  §2 (and the prototype defect of §5.4), the shared caller reference of
  §5.4, and the block lifts that RX does not act on (§5.3).
- The gates of §5.4 ran with the prototype's weaker cover test.
- X and RX need every later-confirmable sink to keep its own witness and
  seed, so they need the analysis to be monotone in K. The G6 drop form
  removes the one known non-monotone filter. Loops are not monotone
  natively (`LoopOutputRestriction.restrictScalar`), but loops are outside
  AC.
- Single-rule arms have one OWASP launch each and no Stirling-PDF or
  Conductor launch. Their time verdicts are weak (design-guide rule 6).
- Stirling-PDF: the provisional comparison rests on one completed native
  launch of this branch and one of an earlier flags-off branch.
- Conductor: one launch per arm, every arm times out in run-8; only the
  time to H7 is compared.
- The residual diagnostic was on in every arm. The rules were not timed
  without it.
- The fail-safe form of the oracle never acted on real code (0 failed
  reads).
- The DECIDED-era G6 fixtures (M4, D5, D6, String chains) were not ported;
  their G6 result is from revision 1.
- Failing tests were not read one by one, except the four cleaner
  fixtures and one RX representation check. The report of every analysis
  was compared, so none of them hides a report change.
- Without canonical order the runs are not deterministic. Early barriers
  vary between launches; the last barriers agreed in every replicate.
- The native stop ends every project at run-11 or earlier. No natural end
  was measured in this revision.
- Project gates shared the host with another agent; all heavy runs held
  one lock, at nice 5.
- ThingsBoard was not run (it fails in run-1 for memory).
