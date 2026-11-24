# Acyclic convergence for the bidirectional analyzer

Status: PROPOSAL, revision 2, 23 November 2026; decisions of 24 November
recorded (§1). It follows the
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

## 0. Summary

Five rules. Each one removes one maker of acyclic demand at its source.

| Rule | Where it acts | Maker it removes | Alone against native: reports | OWASP AC residual alone (native 711-735 rows) |
| --- | --- | --- | --- | --- |
| §5.1 G6 drop form | type filter at a boxed level | none (prerequisite of X and RX) | identical | 729 |
| §5.2 X | forward DEMAND sink witness | DemandTarget renewal at a sink whose owner has a complete ZERO target | identical | 39 (with §5.1) |
| §5.3 RX | relay of a tagged DemandTarget | the same, relayed into a caller | identical | 39, all forward rows 303 → 227 (with §5.1, §5.2) |
| §5.4 MUST-cover | DEMAND reply at a call to an acyclic callee | a DEMAND reply that a NORMAL MUST reply covers | identical | 705 |
| §5.5 EXACT cleaner ignored on MUST | cleaner on a MUST leaf | cleaner survivor | identical, except 4 module fixtures (signed off 24 November) | 24 |
| §5.6 relative C5 cap | — | none: a passenger | — | — |

Combined (configuration AO-C5 = §5.1-§5.5), against native:

| | Native | AO-C5 |
| --- | --- | --- |
| OWASP (3 launches) | `RUN_LIMIT` 11; driver 150.2-153.1 s; residual 711-735 | `RUN_LIMIT` 11; driver 110.7-112.8 s; residual 6 rows / 1 owner; reports identical |
| Stirling-PDF (2 launches) | run-11 stalls: completes after 2,704 s, or times out at 3,000 s; residual 49 | `RUN_LIMIT` 11 after 55.7-56.0 s; residual 5 rows / 3 owners; reports identical to the completed native run |
| Conductor (1 launch) | timeout in run-8; H7 at 666 s; residual 21 (H7) | timeout in run-8; H7 at 600 s; residual 16 rows / 6 owners (H7); reports identical |
| Module suite | 30 analyses / 81 rows open | 18 / 47; 4 cleaner fixtures change (signed off) |
| Rule suite (585) | 2 / 9 | 1 / 8; reports identical |

Driver times include the residual diagnostic (§6). Requirement AC is not
met yet. The open makers are the inside read, the DEMAND STAR start and a
raw depth that follows K (§7).

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
its source. One measured case contradicts the bound: a raw depth that
follows K in an acyclic Conductor method (§5.6, §7 item 3).

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
| Raw depth that follows K | deepens with K | Conductor `ExclusiveJoinTaskMapper#getMappedTasks` | — | open, new (§7 item 3) |
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
(`engine/RunMethodCallServices.kt:527-529`). A block lift and a loop
consumer pass the target on unchanged, with its tag
(`engine/MethodBlockRuntime.kt:548-549`,
`engine/LoopConsumerObservation.kt:85, :118`), and RX does not act there.
So a tagged DemandTarget lifted from a block into a root that has
`ZERO → NormalTarget(id)` is still emitted at the root. Backward source
discharges are untagged and relayed as before.

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

**Gate alone.** Module: 4 report changes, nothing else:
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

**Withdrawal condition of (D).** Look at the cap again if (1) an acyclic
owner has a cut row whose parents are cut rows only, at the same depth,
at two consecutive forward barriers (possible only through
`ap/Reference.kt:253`), or (2) an acyclic owner reaches zero forward rows
with (A) and not with (D) under the same anchor rules.

**New open maker found here.** On Conductor,
`ExclusiveJoinTaskMapper#getMappedTasks` is acyclic by §3, but its raw
output depth equals K in every run:
`ret.Iterable#Element.TaskModel#inputData.Map#MapValue…` repeats until
the global cut (depth 4 at `K = 4`, depth 6 at `K = 6`). The cut row
deepens by one field per round while K grows by two, so it does not end
while K grows. Neither (A) nor (D) acts on it: it is a cut of a DEMAND
selection. The statement or model that repeats `Map#MapValue` is not
traced (§7 item 3).

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
| Conductor | `ExclusiveJoinTaskMapper#getMappedTasks` (1) | raw depth that follows K |
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
3. **Raw depth that follows K (new).** Conductor
   `ExclusiveJoinTaskMapper#getMappedTasks` (§5.6). Trace the statement
   or the model that repeats `Map#MapValue`. Then decide if the case is
   inside the assumption of §1.
4. **The MUST-cover scope reads a call-cone property** (§5.4). This is
   the weak point that withdrew `acC5Exact`. The scope is needed because
   the unscoped rule doubles Conductor's H7 rows; the local cause of that
   growth is not traced.
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
