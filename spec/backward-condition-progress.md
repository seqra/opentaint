# Backward condition progress: MUST requirements and refined MAY seeds

26 November 2026, `saloed/bidirectional`. SPEC AND PROOFS ONLY (user
decision): no ablation, no prototype, no measurement, no WI rule.

Lean: [BackCondRules](lean/ApSpec/BackCondRules.lean) (`BackCond`),
[BackMustRun](lean/ApSpec/BackMustRun.lean) (`BackMust`),
[BackMustView](lean/ApSpec/BackMustView.lean) (`BackMustView`),
[BackNDRefine](lean/ApSpec/BackNDRefine.lean) (`BackND`). All constructive
(`propext`, `Quot.sound` only).

Rules: **B1** a unary literal gives a backward MUST requirement, also for
`[any]`. **B2** backward MUST records. **B3** ND seeds refined by captured
forward inputs. **D1** (§6) is open and needs a user decision.

## 1. Problem

The backward seeds and their layers do not depend on the forward facts.
An `[any]` requirement is DEMAND (W6), so a callee that it enters gets a
DEMAND start, DEMAND summaries, no record, and a selected hand-off row.
The next forward run gets an ANY entry; C2 makes a STAR start that is
DEMAND by itself; the witness stays DEMAND; the seed fires again.

| Real instance (after AO-C5) | Rows | Source |
| --- | --- | --- |
| Stirling-PDF `AuthController#login` and its entry point | 1 + 2 | acyclic-convergence §6, §7 item 2 |
| Stirling-PDF `bytesToWebResponse` arms | not counted | natural-termination §3 |

Not measured: rows per run from `[any]` seeds, reversed `[any]` literals,
ND seeds.

## 2. Definitions

### 2.1 Facts

```text
l = (b, π, t)                 location: base, path, mark
φ = (b, π, κ, μ)              κ ∈ {$, */E, [any]},  μ ∈ {T, *}
x = (φ, E, ℓ)                 E field exclusion,  ℓ ∈ {N, D}
E admits σ    ⇔ σ = [] ∨ σ₀ ∉ E
cov(φ, E)     = { (b, π·σ, t) | κ admits σ ∧ E admits σ ∧ μ admits t }
                $ admits σ ⇔ σ = [];  [any] and * admit every σ
[any-taint]/E (T) ≝ ([any], E, N), μ = T    MUST: every l ∈ cov carries T
[any](T)          ≝ ([any], ∅, D)            MAY
W6: κ = [any] ∧ ℓ = N  ⇒  the fact is [any-taint]
den(j,Ej,g,Eg) = { (l0,l1) | l0 = (j.b, j.π·σ, t) ∈ cov(j,Ej), l1 = (g.b, g.π·τ, μg.out t) ∈ cov(g,Eg),
                   τ = [] if g.κ = $;  τ = σ if g.κ = *;  any τ if g.κ = [any] }
```

### 2.2 Rule conditions

```text
c↓            the condition c with every negated literal := true, as a DNF over positive literals
fires_c(S)    ⇔ ∃ A ∈ c↓. ∀ p ∈ A. ∃ l ∈ S. l ∈ cov(p)
Suff_c(l)     ⇔ ∀ S ∋ l. fires_c(S)  ⇔  fires_c({l})                       [suff_iff]
unary_c(p)    ⇔ [p] ∈ c↓            prod: RulePredicate.isUnary(leaf); legacy sink |patterns| = 1
ND_c(p)       ⇔ ∃ A ∈ c↓. p ∈ A ∧ |A| ≥ 2   prod: isMulti(leaf); legacy sink |patterns| ≥ 2
```

| Claim | Lean (`BackCond`) |
| --- | --- |
| `unary_c(p) ⇒ cov(p) ⊆ Suff_c` | `unary_seed_must` |
| all literals unary ⇒ `⋃ cov(p) = Suff_c` | `unary_cond_exact` |
| ND only: `cov(p) ⊄ Suff_c` | `nd_suff_iff`, `nd_seed_not_must` (cex) |
| every location of a minimal firing state is in `⋃ cov(p)` (MAY cover) | `seed_may_cover`, `core_spec` |
| MUST is relative to `c↓`, not to the signed condition | `firesS_proj`, `signed_not_must` |

A backward requirement `r = (φ, E, ℓ)` at node `n`:

```text
ℓ = N:  ∀ l ∈ cov(φ,E). taint at l at n ⇒ the seeded sink fires        MUST
ℓ = D:  the D facts cover every location of a real route to the sink    MAY
```

### 2.3 Summary edge

```text
e = ⟨d, M, j, Ej, m, g, Eg, ℓ⟩     d ∈ {F, B};  premise j at the entry, conclusion g at the exit of M in P_d
P_F = P,  P_B = rev P;  Fl_d(M)(l0, l1): a flow in P_d from l0 at the entry to l1 at the exit of M
Fl_B(M)(l0, l1) ⇔ Fl_F(M)(l1, l0)                                          [Reverse.flow_rev_iff_calls]
m = must ⇔ j = [any-taint]/Ej       (emitted from a MUST added fact, §3.1)

ℓ = N, m = may :  den(j,Ej,g,Eg) ⊆ Fl_d(M)                                  PAIR-EXACT
ℓ = N, m = must:  ∀ l1 ∈ cov(g,Eg). ∃ l0 ∈ cov(j,Ej). Fl_d(M)(l0, l1)        END-EXACT
ℓ = D          :  coverage only

record(e) ⇔ ℓ = N ∧ |prem(e)| = 1 ∧ (d = F ∨ j ≠ zero)                    R1
            today, d = B also needs: m = may ∧ g has no [any-taint] leaf   (W8 (d), W6)   ← B2 removes it
```

A must record is END-EXACT and not PAIR-EXACT (`BackMust.CexMustPair.cex_must_pair`).
A zero-premise backward edge is never a record: with B1 the N zero-premise
`[any-taint]` seed edge is not a flow (same cex).

## 3. Operations (d = F and d = B use the same rules)

### 3.1 Initial fact emission (ap.md §6.3)

Added fact `a = (φa, Ea, ℓa)` from the binding `b.* → b'.*`; demand entry `D-c` of the callee:

```text
MUST(a) ⇔ φa.κ = [any] ∧ ℓa = N            today d = B: never (W8 (d));  B1: possible   [BackMust.must_seed_bound]
```

| `D-c` mark | `a` mark | premise `j` | `m` | start (ap.md §6.5) |
| --- | --- | --- | --- | --- |
| `*` | any | FLOW form of `D-c`: `$→$`, `[any]→*/{}`, `*/E→*/E`; mark `*` | may | identity, N |
| `T` | `T` | `a ∩ D-c` (below) | must ⇔ MUST(a) ∧ `j.κ = [any]` | must: `(j, Ej, N)`; may: `$`→N, `[any]`→`[any]` D, `*/E (T)`→`[any]` D |
| `T` | other | none | | |

```text
a ∩ D-c,  p = D-c.π, t = D-c.κ:
  a.π = p·r, r ≠ []          a            if t admits r, else ⊥
  a.π = p                    p, meet(a.κ, t)
  p = a.π·r, r ≠ []          p, meet(a.κ, t)   if a.κ and Ea admit r, else ⊥
meet(a.κ, t)           t = $    t = [any]          t = */E2
  $                    $        $                  $
  [any]                $        [any]              */E2
  [any-taint]/E1       $        [any-taint]/E1     (no canonical case)
  E1 stays at the added path; at a deeper demand path the exclusion is ∅
```

C2: every common location with its mark is covered by `j`, `a` satisfies `j`,
`j ⊆ D-c` (`AnyTaintExCov.emitX_contract`).

### 3.2 Summary edge ∩ demand edge (ap.md §6.4, restricted runs)

Demand edge `δ = (D-c, D-p)` of the callee. Persistence (R1) and selection
(§3.5) read the raw `e`, before this operation.

```text
restrict(e, δ) = ⊥   if D-p = ⊥
                    ∨ ¬(cov(j,Ej) ⊆ cov(D-c) ∧ μj ⊆ μ(D-c))      whole premise inside, reads Ej
                    ∨ ¬meet(μg, μ(D-p))                             T~U ⇔ T = U;  * meets all
                    ∨ g.b ≠ D-p.b
               = ⟨d, M, j, Ej, m, cut(g, D-p), ℓ⟩                     j, m, ℓ kept
```

| `g` against `D-p` (`p = D-p.π`) | `cut(g, D-p)` |
| --- | --- |
| at `p` | at `p`, tail meet below |
| below, `g.π = p·r` | `g` if `D-p.κ` admits `r`, else ⊥ |
| above, `p = g.π·r`, `g.κ = [any]` | at `p`: `$` if `D-p.κ = $`, else `[any]` |
| above, `g = [any-taint]/E` | ⊥ if `E` rejects `r`; else at `p`: `$` / `[any-taint]/E2` / `[any-taint]/∅` for `$` / `*/E2` / `[any]` demand |
| above, `g.κ = */E` | `g` if `E` admits `r`, else ⊥ |
| above with `g.κ = $`; apart; other base | ⊥ |

| tail meet at `p` | `$` demand | `*/E2` demand | `[any]` demand |
| --- | --- | --- | --- |
| `$` | `$` | `$` | `$` |
| `[any]` | `$` | `[any]` | `[any]` |
| `[any-taint]/E` | `$` | `[any-taint]/(E∪E2)` | `[any-taint]/E` |
| `*/E` | `*/E` | `*/E` | `*/E` |

C5: every pair of `e` whose exit is in `cov(D-p)` with its mark is a pair of
the result; the result adds no pair (`HandoffRestrict.restrictI_contract`,
`restrictI_sub`; `CurrentDemand.restrictCertificate`). Limits: `[any]` over
`*/E2` loses `E2`; a `*` conclusion stays whole; an abstract mark stays
pass-through. With B1 the `[any-taint]` rows apply in d = B too.

### 3.3 Application in the own direction (MUST rules)

```text
inside(j;a)     ⇔ cov(j,Ej) ⊆ cov(a,Ea) ∧ μj ⊆ μa                        [AnyTaintEx.satX]
applicable(j;a) ⇔ cov(a) ⊆ cov(j) ∧ (j.κ = [any] ⇒ a.κ = [any])         [applicable]

run piece  e' = restrict(e, δ):   needs inside(j;a)
record     e  (R4, later runs):   needs inside(j;a) ∨ applicable(j;a)
r ∈ a ∘ (j → g):   ℓr = ℓa ∨ ℓg
MUST rule:  m = must ∧ ¬inside(j;a)  ⇒  ℓr := D,  Er := ∅                [AnyTaintEx.recLayerX]
```

END-EXACT names only SOME `l0 ∈ cov(j)`; only `inside` makes every `l0`
carry the mark (`AnyTaintExact.CexApp.cex_app`). The rule is the same for
d = F (today) and d = B (B2). Soundness and exactness of the N results:
`AnyTaintExExact.DRX_edgeOK` (F), `BackMust.DBX_edgeOK_nz` (B).

### 3.4 Read view in the opposite direction (R3, MUST rules)

```text
view(e), e a normal record read in direction d̄:
  premise'    = g                              if g.κ = $
              = (g.b, g.π, */Eg, μg)           if g = [any-taint]/Eg
  conclusion' = (j, N)                         if j.κ = $
              = ((j.b, j.π, [any], μj), D)     if m = must        (Ej forgotten)
  guard: μj, μg concrete; tails ∈ {$, [any-taint]}; ≥ 1 [any-taint]; a $ side has E = ∅
         else the generic leaf reversal (ap.md §9.1)
  ℓr = ℓa ∨ ℓ(conclusion')
```

| `e` | `view(e)` | Lean |
| --- | --- | --- |
| `j.κ = $` | exact converse, N | `CurrentMustReverse.exact_converse` |
| `m = must`, d = F (today) | sound, D only, not exact | `CurrentMustReverse.must_application_demand`, `AnyTaintExact.CexRev.cex_rev` |
| `m = must`, d = B (**B2**) | sound, D only, not exact | `BackMustView.viewF_demand`, `viewF_stays_demand`, `viewF_sound`, `Cex.viewF_not_exact` |

### 3.5 Hand-off selection (F77, ap.md §8.5)

```text
sel(e) ⇔ ℓ = D ∨ |prem(e)| ≥ 2 ∨ (d = B ∧ j = zero)
sel(e)  ⇒ each piece restrict(e, δ) = ⟨j → g'⟩ gives the next-run demand edge (D-c = g', D-p = j),
          tails normalized: [any-taint]/E → [any]
¬sel(e) ⇒ record(e): no callee demand; the next run reads e (R4) or view(e) (R3)
```

With B2, a backward must summary has `¬sel(e)`. See D1 (§6).

## 4. Rule table

Run `n` is backward; run `n−1` is the forward run before it. **Bold** = new.

### 4.1 Sinks: seeds at `(M, s)`

| # | Rule condition | Emitted backward fact | Today | Forward run `n−1` |
| --- | --- | --- | --- | --- |
| K1 | `ContainsMark(P,T)`, unary | `P.$(T)` N | same | DEMAND witness `W` of the sink at `(M, s, occ)` |
| K2 | `ContainsMarkOnAnyField(P,T)`, unary | **`P.[any-taint](T)` N, `E = ∅`** | `P.[any](T)` D | `W` |
| K3 | `ContainsMark(P,T)` in an ND alternative | `P.$(T)` N (zero premise, never a record) | same | `W` (refinement is the identity) |
| K4 | `ContainsMarkOnAnyField(P,T)` in an ND alternative | **`refine_j(Cap)` D (§5)** | `P.[any](T)` D | `W` and `Cap_j(M, s, occ)` |
| K5 | literal unary and ND | K1 / K2 only | — | `W` |
| K6 | no positive literal; unconditional (zero pattern) | none (zero demand covers it) | same | `W` |
| K7 | end-fact trigger of alternative `A` (row S8 fired) | K1–K4 with `Cap = ∅` | K1–K4 today | none |
| K8 | GROUP-projected sink (`fullSinkSeedsFor`) | K1–K4 with `Cap = ∅` | K1–K4 today | `W` |

### 4.2 Reversed statement rules: input requirement `r` on the target, layer `ℓr`

| # | Rule condition | Emitted backward fact | Today | Forward run `n−1` |
| --- | --- | --- | --- | --- |
| S1 | unconditional source `zero → P.t(T)`, `t ∈ {$, [any-taint]}` | zero fact (zero demand); source hit | same | none (run `n+1` fires it only if hit) |
| S2 | conditional source, unary `ContainsMark(Q,T')` → `P.t(T)` | `Q.$(T')` in `ℓr` | same | none |
| S3 | conditional source, unary `ContainsMarkOnAnyField(Q,T')` → `P.t(T)` | **`Q.[any-taint](T')` in `ℓr`** | `Q.[any](T')` D | none |
| S4 | conditional source, ND literal `ContainsMark(Q,T')` | `Q.$(T')` D | same | (refinement is the identity) |
| S5 | conditional source, ND literal `ContainsMarkOnAnyField(Q,T')` | **`refine_j(Cap)` D (§5)** | `Q.[any](T')` D | `Cap_j(M, s, occ)` of the source |
| S6 | pass rule `P → Q` (no `AnyField`) | reversed result in `ℓr` | same | none |
| S7 | pass rule `P → Q.AnyField` | every result D (MAY class) | same | none |
| S8 | end-fact action of sink alternative `A` | zero fact; fire K7 at `(M, s, A)` once | same | none (also if `A` is CONFIRMED) |
| S9 | cleaner, type filter | as today | same | none |

MAY class = S4, S5, S7: every result D, also a `$` result (DES-3, D18).

### 4.3 Calls: requirement `c` binds into a callee by `b.* → b'.*`

`δ = (D-c, D-p)`: callee demand edge from the hand-off of forward run `n−1`.

| # | `c` | `D-c` | premise `j`, `m` | start | exit summary `e` | Today |
| --- | --- | --- | --- | --- | --- | --- |
| C1 | `x.[any-taint]/E(T)` N | concrete `[any](T)` | **`[any-taint]/E` must** | **N** | **END-EXACT, record (B2); hand-off: D1** | `c` is `x.[any](T)` D → C4 |
| C2 | `x.[any-taint]/E(T)` N | concrete `$(T)` | `$` may | N | PAIR-EXACT, record; results in the caller **N** | same `j`, `e`; results D (input D) |
| C3 | `x.[any-taint]/E(T)` N | abstract `*` | FLOW `*/{}` may | identity N | PAIR-EXACT FLOW record; results in the caller **N** | results D (input D) |
| C4 | `x.[any](T)` D | concrete `[any](T)` | `[any]` may | D | D, `sel(e)` | same |
| C5 | `x.$(T)` N | concrete | `$` may | N | PAIR-EXACT, record | same |

The return to the caller uses §3.3 (own-direction records) and §3.4
(forward records read backward), unchanged.

## 5. B3: ND refinement

```text
Cap_j(M,s,occ) = { (a, Ea) | a satisfied literal j in a COMPLETED combination (N or D) of occ at (M,s) in run n−1 }
  normal form: μa := the concrete mark that the check matched (FLOW input: the literal mark)
               a.*/E := a.[any]/E
refine_j(Cap) = { a ∩ p_j | (a,Ea) ∈ Cap_j } ∖ {⊥}    if Cap_j ≠ ∅        (a ∩ p_j: §3.1 concrete row)
              = { p_j }                                if Cap_j = ∅        fallback B3-F
layer: D for p_j.κ = [any], E forgotten;  p_j.κ = $ ⇒ a ∩ p_j = p_j (no change)
```

Capture site: `CompletePredicateBinding.leaves`/`.inputs`
(`RulePredicateStore.kt:99`), legacy `ConjunctionStore.CompleteBinding`;
held past `freeze()` as a hand-off side table, outside `Seed` equality.

| Claim | Lean (`BackND`) |
| --- | --- |
| `cov(a ∩ p) = cov(a) ∩ cov(p)` for a concrete `a` | `meetLit_inter` |
| `refine_j ⊆ p_j`; a meet `⊆` its input; E forgotten still `⊆ p_j` | `refine_inside`, `meetLit_forget_inside` |
| `Real_j ⊆ cov(p_j) ∩ cov(Cap_j) ⇒ Real_j ⊆ cov(refine_j)` | `refine_sound`, `refine_sound_strict`, `forwardCaptured_of_combos` |
| `Cap' ⊑ Cap ∧ dom Cap ⊆ dom Cap' ⇒ refine(Cap') ⊑ refine(Cap)` | `refine_mono`, `refine_mono_seq` |
| deterministic; paths from `p_j` or `Cap`; `≤ |Cap| + |lits|` seeds; legal seeds | `refine_det`, `refine_det_set`, `refine_shape`, `refine_length`, `refine_legal` |
| contract B and the iteration theorem with refined seeds | `B_general_refined`, `iteration_general_refined` |
| selected proof only: a real location is lost | `Vec.cex_selected_only` |
| `*` mark capture: no seed at all; `*/E` capture: illegal seed | `Vec.cex_abstract_mark`, `Vec.cex_star_capture` |
| `dom Cap` shrinks ⇒ the fallback grows the seed | `Vec.cex_mono_fallback` |

Not selected: B3-P (fallback = the previous seed, and every seed met with
it): monotone by construction, keeps seed state across runs, can remove a
demand that today keeps (S-H6).

## 6. D1: hand-off of a backward MUST record (OPEN, unselected change)

```text
B2 ∧ F77 unchanged:  ¬sel(e) for e = ⟨B, M, [any-taint]/E, must, g, N⟩
  ⇒ run n+1 does not re-analyse M; it reads only view(e), which is D (§3.4)
cex_drop_forward_demand: callee ret.f.g = arg0;  caller a = arg0.x $ (T) N;  sink ContainsMarkOnAnyField(ret, T)
  FL 1, with the callee demand:  ret.f.[any] D
  FL 3, with the callee demand:  ret.f.g.x $ (T) N   → sink N   (CONFIRMED today)
  view(e), no callee demand:     ret.[any] (T) D     → sink D   (stays provisional)
```

Only a backward MUST record has this defect: a forward must record feeds
the backward run, which confirms nothing; a `$`-premise record has an exact
view.

| Option | `sel(e)` for a backward must `e` | Results | Rows removed |
| --- | --- | --- | --- |
| H1 | F77 unchanged: false | can lose a confirmation | yes |
| H1g | true unless a N, PAIR-EXACT, complete forward record of `M` covers `g` | kept (`BackMustView.guard_keeps_normal`, canonical FLOW records; `Cex.guard_instance`) | small: F77 already drops that demand today |
| H2 | true | kept, except S-H1 | none |
| H3 | false + a new forward rule: an exists-any tail, or a confirmation where a forward N fact meets a backward MUST requirement, with a trace | can keep it | yes; changes the forward run, the sink check, trace resolution; not designed |

Recommendation: prototype B1 + B2 + B3 with H2, and log in shadow mode the
callee demands that H1 would drop and whether the status-quo forward run gets
an N callee summary under them. No case on all projects and suites ⇒ gate H1.
A case ⇒ withdraw H1; the §1 owners need H3.

## 7. Semantic scope

| Changed (selected by the user, 26 Nov) | Rows |
| --- | --- |
| unary `[any]` sink seed: D → N MUST | K2 |
| reversed unary `[any]` source literal: D → `ℓr` MUST | S3 |
| backward MUST added fact, must-premise, N start | C1, §3.1 |
| backward MUST records: R1, R4, R3 view | C1, §2.3, §3.3, §3.4 |
| ND `[any]` seeds and reversed ND `[any]` literals refined | K4, S5, §5 |
| hand-off of a backward MUST record | D1 (open) |

Unchanged: the forward run (transfer, sink check, layers, records, views
of forward records, confirmation, traces); the MAY class (S4, S5, S7);
`$` seeds; zero rows; source hits; C1–C5; §3.1–§3.2 tables; field limits
and FL+1 caps; hand-off normalization; W8 (d) for demand patterns
(`Demand.kt:41`, `DemandStore.kt:449`); confirmed and provisional results
(the gate).

| Invariant | Change |
| --- | --- |
| interpreter.md I11 (f), I14 ("the backward run has no `[any-taint]`"), §4.9 | K2, S3, K4, S5; "no micro edge has the premise tail `[any-taint]`" stays |
| `MicroEdge.kt:23-25` A1 | a reversed micro edge may have a must target (S3), never a must premise |
| ap.md §6.5 ("the backward run has no `[any-taint]` premise") | C1 |
| ap.md §8.7 R1, `RecordStore.kt:274-277` | §2.3 |
| ap.md §9.1 backward W6 | only the MAY class and non-B1 `[any]` results |
| ap.md §8.5 F77 | H1: none; H1g/H2: one condition |
| Lean iteration theorems (`Backward.B_general`, `W6.iteration_general6`, `Handoff*`) | not re-proved with B2 records; `Handoff.CrossK .any = False`, so `Handoff.demOfN` hands a must record off (= H2) |

| Hidden-change candidate | Status |
| --- | --- |
| S-H1: a backward `[any-taint]/E` gets an exclusion at a strong update; `[any]` D does not. `x.f = z; …; x.f = y; sink(x)`: MUST gives no requirement on `z`, D gives one. The forward demand can get narrower. | base model: same facts (`W6.D6_same_shape`, `summaryDemand_iff`); refined model: not proved; shadow-compare the normalized pieces |
| S-H2: the EXACT-cleaner rule for a MUST leaf (`Clean.kt:187-192`) now runs backward | not modelled |
| S-H3: a must and an `[any]` premise at one path are separate keys | cost only |
| S-H4: MUST is relative to `c↓` | the forward run uses `c↓` too |
| S-H5: B1 under-approximates MUST (`nd_overlap_suff`) | sound |
| S-H6: B3 narrows the forward demand | not proved; measure |
| S-H7: new record shape `(B, [any-taint] premise)` | no dedup change for existing shapes |
| S-H8 (H1 only): traces through a backward must view | check in the prototype |

## 8. Proof map: run level and views

| Claim | Lean |
| --- | --- |
| a N result of the backward transfer is a forward refined result | `BackMust.transferXB_normal` |
| K2 seed is N; bound: MUST added; must-premise with N start; today: D start | `must_seed_normal`, `bindX_star_any`, `must_seed_bound`, `must_premise_normal`, `demand_seed_contrast`, `demand_premise_start` |
| every N backward edge with a non-zero premise: PAIR-EXACT (may) / END-EXACT (must) on `rev P` | `DBX_edgeOK_nz`, `edge_exactBX_gen`, `no_zero_summaryX` |
| backward records are exact, also over a run sequence | `recsB_exact`, `recsB_must_end`, `recsB_pair`, `recsB_next`, `recsBSeq_ok` |
| in `P`: `∀ l ∈ cov(gb). ∃ l0 ∈ cov(jb). Fl_F(M)(l, l0)` | `backMust_forward`, `backPair_forward`, `backMust_forward_valid`, `backMust_forward_seq` |
| S3 MUST for every target kind; S4, S7 not MUST (cex), sound MAY | `BackCond.rev_unary_source_must`, `rev_nd_source_not_must`, `rev_pass_any_not_must`, `rev_pass_may_sound` |
| §3.4, §6 | `BackMustView` (§3.4 table, D1 table) |

Hypotheses of `DBX_edgeOK_nz`: those of `DRX_edgeOK` on `rev P`, plus
`NoZeroIn` (= `NoZeroBack P`, I11 (c); necessary: `BExact.CexZeroBack`)
and `SeedsConcB` (necessary: `BExact.CexSeed`); record hypotheses only off
the zero base, discharged by `recsBSeq_ok`.

Model vs production:

* The run-level model gives the forward `AnyField` target the meaning
  "every location", so its reversal is exact there and the theorems hold
  for every MAY class. The rule level proves the MAY class (S4, S5, S7)
  is not MUST. Link (argued): an N backward fact never crosses a MAY-class
  edge.
* The must flag of a seed is an input of `BackMust`; `BackCond` decides it
  on `c↓` (DNF). Production has an NNF DAG.
* `BackMustView`: one record, one leaf; no store lookup, statics, cleaners,
  type filters; `guard_keeps_normal` only for canonical FLOW records.
* `BackND`: the base model has no ND sink; each literal is its own sink.
  The ND form of the backward contract is not proved. `refine_mono` keeps
  the meet exclusions; production forgets them.
* Not modelled: S-H2, GROUP projection, end-fact triggers, statics.

## 9. Gate, withdrawal, checklist

Gate per rule, alone, per project (OWASP, Stirling-PDF, Conductor,
ThingsBoard) and the module, jvm and rule suites: identical confirmed and
provisional results; wall time and peak memory not worse. Withdraw a rule
that fails. H1: also withdraw on one shadow case (§6). B3: also on a
capture heap cost that is worse in peak memory.

```text
[x] Failure class and real trace        §1 (per-run counts not measured)
[ ] Ablation                            not done (spec only)
[ ] Native prototype                    not done (spec only)
[ ] Execution site and measured volume  sites: seeds per run, transfer per backward fact,
                                        records per barrier, replay per call offer,
                                        capture per completed combination; volumes not measured
[x] Semantic scope                      §7; D1 open
[x] Proof scope, model vs production    §8
[x] Withdrawal condition                §9
[ ] WI classification                   none
[x] Proofs                              §2-§8
```

Blind spots: nothing ran natively; with H2, B1/B2 remove no forward row;
the H1 risk is a reduction, not a measured case; S-H1, S-H2, S-H6, S-H8
and the B3 heap cost are not measured.
