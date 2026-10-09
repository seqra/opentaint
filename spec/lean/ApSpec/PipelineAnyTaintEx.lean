/-
  ApSpec.PipelineAnyTaintEx — the closures of the `[any-taint]` conclusion WITH AN EXCLUSION (decision
  F69, DESIGN §6 amendment A2) as instances of the communication pipeline (`ApSpec.Pipeline`,
  analyzer-core.md §5, §12).

  `AnyTaintExDefs.lean` gives two refined closures: run 1 with annotated facts (`D6X`, over the
  objects `XObj6`) and the restricted forward run with must-premises and exclusions (`DRX`, over
  the objects `XObj`; the spec instance is `DRXs`). This file encodes them as pipeline systems, as
  `PipelineAnyTaint.lean` does for `D6T` and `DRT`. So the pipeline theorems
  (`Pipeline.reach_sound`, `quiescent_exact`, `no_lost_join`) apply to them: at quiescence the
  analyzer computes exactly `D6X` and `DRX`.

  The objects of `D6X` are not the objects `Obj` of `D` (an edge has an annotated fact `XFact`), so
  `sysD6X` has its own pipeline objects (`XPObj6`) and its own rules; it is not `sysD` with other
  local rules (as `sysD6T` is).

  ## 1. Run 1 with the exclusion: `sysD6X`

  The objects are `XPObj6`, over the objects `XObj6` of `D6X`:
    * `base o`               an object of `D6X`; owner: its method;
    * `link m a aex M ic`    the callee `m` holds the link: the added fact `a` with the exclusion
                             `aex` of the bound fact, from a caller edge of `M` with the premise
                             `ic`; owner `m`;
    * `sub M i n' c a`       the caller's subscription: a caller edge with the premise `i` at the
                             call `c` (return node `n'`) binds the annotated fact `a`; owner `M`,
                             topic `c.callee`;
    * `pub m j g`            a published summary edge `j → g` of `m` (`g` annotated); owner `m`,
                             topic `m`.

  | closure rule (`D6X`)             | pipeline                                          | owner of the premises → conclusion |
  |----------------------------------|---------------------------------------------------|------------------------------------|
  | root                             | root `base (init M zero)`                         | – → M                              |
  | start (`startX`), step, reqStmt  | local rule on `base` objects                      | M → M                              |
  |   (`transferX`), pass, clean,    |                                                   |                                    |
  |   reqClean (`cleanResX`), filt,  |                                                   |                                    |
  |   reqSink, vuln (`checkX`)       |                                                   |                                    |
  | answer                           | local rule `[req M i t, added M a]`               | M → M                              |
  | initA                            | local rule `[added m a]`                          | m → m                              |
  | added                            | `[edge M ic n f]` → `link c.callee a.af.fact a.ex M ic` (`a ∈ bindX f e`) | M → callee (MESSAGE) |
  |                                  | `[link m a aex M ic]` → `added m a`               | m → m                              |
  | reqUp (`overlapX`)               | local rule AT THE CALLEE `[req m j t, link m a aex M ic]` → `req M ic t` | m → M (MESSAGE) |
  | ret                              | `[edge M i n f]` → `sub M i n' c a`               | M → M                              |
  |                                  | `[init m j, edge m j (exit m) g]` → `pub m j g`   | m → m                              |
  |                                  | JOIN `[sub M i n' c a]` `(pub c.callee j g)`, with `applicable j a.af.fact` → `edge M i n' (limitFX r')` | M, topic callee |

  What each object carries. The added fact of run 1 is a `PFact` (`D6X.added` drops the
  exclusion), but `D6X.reqUp` reads the exclusion of the bound fact (`overlapX a.af.fact a.ex j`).
  So a link carries the added fact AND the exclusion `aex` of the bound fact; `added` forgets
  `aex`. A subscription carries the whole annotated bound fact (the join reads `a.af.fact` in
  `applicable` and the whole `a` in `applySummaryX`). A publication carries the annotated exit fact
  (`applySummaryX` reads its exclusion). Run 1 is a forward run: no zero subscription, no zero
  publication.

  ## 2. The restricted forward run with must-premises and exclusions: `sysDRX`

  The objects are `XPObj`, over the objects `XObj` of `DRX`:
    * `base o`                     an object of `DRX`; owner: its method;
    * `link m a am aex M ic`       the callee `m` holds the link: the added fact `a` with its flag
                                   `am` (`[any-taint]`: `.any` and normal on its link) and its
                                   exclusion `aex`, from a caller edge of `M` with the premise
                                   `ic`; owner `m`;
    * `sub M i mi iex n' c a`      the caller's subscription: a caller edge with the premise
                                   `(i, mi, iex)` at the call `c` (return node `n'`) binds the
                                   annotated fact `a`; owner `M`, topic `c.callee`;
    * `pub m j mj jex g`           a published summary edge `(j, mj, jex) → g` of `m`, after the
                                   restriction by a demand edge of `m`; owner `m`, topic `m`.

  | closure rule (`DRX`)             | pipeline                                          | owner of the premises → conclusion |
  |----------------------------------|---------------------------------------------------|------------------------------------|
  | root                             | root `base (init M zero false {})`                | – → M                              |
  | start (`startX`), step, reqStmt  | local rule on `base` objects                      | M → M                              |
  |   (`transferX`), pass, clean,    |                                                   |                                    |
  |   reqClean, filt, reqSink, vuln  |                                                   |                                    |
  | answer (`overlapX`)              | local rule `[req M i t, added M a am aex]` → `init M (answerInit i a t) false {}` | M → M |
  | initR (`emitTX emit`)            | local rule `[added m a am aex]` → `init m j mj jex` | m → m                            |
  | retRec (`recLayerX`)             | local rule `[edge M i mi iex n f]` (records are fixed) | M → M                         |
  | added                            | `[edge M ic mc icx n f]` → `link c.callee a.af.fact am a.ex M ic`, with `am = a.af.fact.kind.isAny && !a.af.demand` | M → callee (MESSAGE) |
  |                                  | `[link m a am aex M ic]` → `added m a am aex`     | m → m                              |
  | reqUp (`overlapX`)               | local rule AT THE CALLEE `[req m j t, link m a am aex M ic]` → `req M ic t` | m → M (MESSAGE) |
  | ret                              | `[edge M i mi iex n f]` → `sub M i mi iex n' c a` | M → M                              |
  |                                  | `[init m j mj jex, edge m j mj jex (exit m) g]`, with `demand m d`, `restrict j jex g d = some g'` → `pub m j mj jex g'` | m → m |
  |                                  | JOIN `[sub M i mi iex n' c a]` `(pub c.callee j mj jex g)`, with `sat j jex a.af.fact a.ex` → `edge M i mi iex n' (limitFX r')` | M, topic callee |

  What each object carries. A link carries the added fact with its flag `am` and its exclusion
  `aex` (`added`, `initR` and the emission read all three; `answer` and `reqUp` read `a` and `aex`)
  and the caller premise `ic` (`reqUp` reads it). It does not carry the must flag `mc` and the
  exclusion `icx` of the caller premise: no rule reads them (the request `req M ic t` has neither).
  A subscription carries the caller premise with its must flag `mi` and its exclusion `iex`: the
  result of the join is an edge of the premise `(i, mi, iex)`. It carries the whole annotated bound
  fact `a` (the join reads `a.af.fact` and `a.ex` in `sat` and the whole `a` in `applySummaryX`). A
  publication carries the callee premise with its must flag `mj` and its exclusion `jex` and the
  annotated (restricted) conclusion `g`: the join reads `j` and `jex` (`sat`, `applySummaryX`) and
  `g`; it does not read `mj` (`DRX.ret` only carries it: in the spec the premise `[any-taint]` and
  the premise `[any]` are different premise keys, DESIGN §5). The layer of the result is that of
  `applySummaryX` and `limitFX`, as in `DRX.ret`. The rule for a record is local at the caller: the
  records are a fixed predicate, and the demotion `recLayerX` of a must record applied by
  `applicable` only reads the record and the bound fact. `DRX` is a forward run, so `sysDRX` has no
  zero subscription and no zero publication.

  ## Main theorems (all parameters of the closures are variables)

    * `sysD6X_wf`, `sysDRX_wf`: the systems are well formed (`Sys.WF`).
    * `clD6X_iff`: `Cl sysD6X (.base o) ↔ D6X o`; `clDRX_iff`: `Cl sysDRX (.base o) ↔ DRX o`.
    * The other objects: `clD6X_link`, `clD6X_sub`, `clD6X_pub`; `clDRX_link`, `clDRX_sub`,
      `clDRX_pub`: a link, a subscription and a publication are exactly the data that the closure
      rules read.
    * The pipeline theorems for these systems: `known_D6X`, `known_DRX` (`Pipeline.reach_sound`);
      `result_D6X`, `result_DRX`, `result_DRXs` (`Pipeline.quiescent_exact`: at a reachable
      quiescent state the processed `base` objects are exactly `D6X` / `DRX` / the spec instance
      `DRXs`); `no_lost_summary_D6X`, `no_lost_summary_DRX` (`Pipeline.no_lost_join`).
    * §5: a normal `[any-taint]/{name}` edge (the source, then the strong write `this.name = v`,
      the setter vector of `AnyTaintExDefs.Vec`) is in both pipeline closures, so the encodings are
      not vacuous on the exclusion.

  All proofs are constructive (`propext`, `Quot.sound` only; see the `#print axioms` lines).
-/
import ApSpec.PipelineProofs
import ApSpec.PipelineAP
import ApSpec.AnyTaintExDefs

namespace ApSpec.PipelineAnyTaintEx
open ApSpec ApSpec.Pipeline ApSpec.PipelineAP ApSpec.AnyTaint ApSpec.AnyTaintEx

deriving instance DecidableEq for XObj6
deriving instance DecidableEq for XObj

/-! ## 1. Run 1 with the exclusion: the closure `D6X` -/

/-- The method of an object of `D6X`. -/
def xobj6Owner : XObj6 → MethodId
  | .init M _ => M
  | .edge M _ _ _ => M
  | .added M _ => M
  | .req M _ _ => M
  | .vuln M _ _ _ => M

/-- The pipeline objects of `D6X` (an edge, a subscription and a publication carry annotated
    facts; a link carries the exclusion of the bound fact). -/
inductive XPObj6 where
  /-- an object of `D6X`; owner: its method -/
  | base (o : XObj6)
  /-- the callee `m` holds the link: the added fact `a` with the exclusion `aex` of the bound
      fact, from a caller edge of `M` with the premise `ic` -/
  | link (m : MethodId) (a : PFact) (aex : Excl) (M : MethodId) (ic : PFact)
  /-- the caller's subscription: caller premise `i`, return node `n'`, call `c`, annotated bound
      fact `a` -/
  | sub  (M : MethodId) (i : PFact) (n' : Node) (c : Call) (a : XFact)
  /-- a published summary edge `j → g` of `m` (`g` annotated) -/
  | pub  (m : MethodId) (j : PFact) (g : XFact)
deriving DecidableEq

/-- The owner of a pipeline object of `D6X`. -/
def XPObj6.owner : XPObj6 → MethodId
  | .base o => xobj6Owner o
  | .link m _ _ _ _ => m
  | .sub M _ _ _ _ => M
  | .pub m _ _ => m

def XPObj6.isSub : XPObj6 → Bool
  | .sub .. => true
  | _ => false

def XPObj6.isPub : XPObj6 → Bool
  | .pub .. => true
  | _ => false

/-- The topic: the callee of a subscription, the publisher of a publication (and the owner for
    the other objects, which never meet a topic). -/
def XPObj6.topic : XPObj6 → MethodId
  | .base o => xobj6Owner o
  | .link m _ _ _ _ => m
  | .sub _ _ _ c _ => c.callee
  | .pub m _ _ => m

/-- The roots of run 1: the zero fact of each root method. -/
def rootsX6 (roots : List MethodId) : List XPObj6 :=
  roots.map (fun M => .base (.init M zeroFact))

theorem mem_rootsX6 {roots : List MethodId} {x : XPObj6} (h : x ∈ rootsX6 roots) :
    ∃ M, M ∈ roots ∧ x = .base (.init M zeroFact) := by
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1 h
  exact ⟨M, hM, rfl⟩

theorem root_mem_rootsX6 {roots : List MethodId} {M : MethodId} (h : M ∈ roots) :
    (.base (.init M zeroFact) : XPObj6) ∈ rootsX6 roots :=
  List.mem_map.2 ⟨M, h, rfl⟩

section SysD6X
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- The local rules of `D6X`. -/
inductive RuleX6 : List XPObj6 → XPObj6 → Prop where
  | start {M i} :
      RuleX6 [.base (.init M i)] (.base (.edge M i (P.entry M) (startX i false Excl.empty)))
  | step {M i n f n' s f'} : (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transferX taint counted L s f).facts →
      RuleX6 [.base (.edge M i n f)] (.base (.edge M i n' f'))
  | reqStmt {M i n f n' s t} : (M, n, Instr.stmt s, n') ∈ P.edges →
      t ∈ (transferX taint counted L s f).reqs →
      RuleX6 [.base (.edge M i n f)] (.base (.req M i t))
  | pass {M i n f n' c} : (M, n, Instr.call c, n') ∈ P.edges →
      memB f.af.fact.base c.touched = false →
      RuleX6 [.base (.edge M i n f)] (.base (.edge M i n' f))
  /-- the caller sends the link to the callee (a message): the added fact with the exclusion of
      the bound fact -/
  | link {M i n f n' c e a} : (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (bindX f e).facts →
      RuleX6 [.base (.edge M i n f)] (.link c.callee a.af.fact a.ex M i)
  /-- the callee stores the added fact of a link (run 1: the `PFact` only) -/
  | added {m a aex M ic} : RuleX6 [.link m a aex M ic] (.base (.added m a))
  | initA {m a} : RuleX6 [.base (.added m a)] (.base (.init m (α m a)))
  /-- the caller subscribes at the call, with the annotated bound fact -/
  | sub {M i n f n' c e a} : (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (bindX f e).facts →
      RuleX6 [.base (.edge M i n f)] (.sub M i n' c a)
  /-- the callee publishes a summary edge -/
  | pub {m j g} : RuleX6 [.base (.init m j), .base (.edge m j (P.exit m) g)] (.pub m j g)
  | reqSink {M i n f s t} : (M, n, s) ∈ sinks → checkX i f s = .request t →
      RuleX6 [.base (.edge M i n f)] (.base (.req M i t))
  | answer {M i t a} : a.mark = .conc t → overlapB a i = true →
      RuleX6 [.base (.req M i t), .base (.added M a)] (.base (.init M (answerInit i a t)))
  /-- the callee climbs a request through a link (the conclusion is a message to the caller); the
      overlap reads the exclusion of the bound fact -/
  | reqUp {m j t a aex M ic} : climbsB a.mark t = true → overlapX a aex j Excl.empty = true →
      RuleX6 [.base (.req m j t), .link m a aex M ic] (.base (.req M ic t))
  | vuln {M i n f s} : (M, n, s) ∈ sinks → checkX i f s = .triggered →
      RuleX6 [.base (.edge M i n f)] (.base (.vuln M n s f.af.demand))
  | clean {M i n f n' cl f'} : (M, n, Instr.clean cl, n') ∈ P.edges →
      f' ∈ (cleanResX cl f).facts →
      RuleX6 [.base (.edge M i n f)] (.base (.edge M i n' f'))
  | reqClean {M i n f n' cl t} : (M, n, Instr.clean cl, n') ∈ P.edges →
      t ∈ (cleanResX cl f).reqs →
      RuleX6 [.base (.edge M i n f)] (.base (.req M i t))
  | filt {M i n f n' b may} : (M, n, Instr.filt b may, n') ∈ P.edges →
      (f.af.fact.base = b → may f.af.fact.path = true) →
      RuleX6 [.base (.edge M i n f)] (.base (.edge M i n' f))

/-- The join of `D6X` (the rule `ret`): the run-1 `applicable` on the bound fact, the refined
    summary application `applySummaryX`, the binding back `bindX`, the field limit `limitFX`. -/
inductive JoinX6 : List XPObj6 → XPObj6 → XPObj6 → Prop where
  | ret {M i n' c a j g r e2 r'} : applicable j a.af.fact = true →
      r ∈ (applySummaryX a j Excl.empty g).facts → e2 ∈ c.fromCallee → r' ∈ (bindX r e2).facts →
      JoinX6 [.sub M i n' c a] (.pub c.callee j g) (.base (.edge M i n' (limitFX counted L r')))

/-- Run 1 with the exclusion as a pipeline system. -/
def sysD6X : Sys XPObj6 MethodId MethodId where
  owner := XPObj6.owner
  roots := rootsX6 roots
  rule  := RuleX6 P taint counted L α sinks
  isSub := XPObj6.isSub
  isPub := XPObj6.isPub
  topic := XPObj6.topic
  join  := JoinX6 counted L

/-- What a link of run 1 means: a caller edge of `M` with the premise `ic`, at a call of `m`, binds
    an annotated fact `a'` whose path fact is `a` and whose exclusion is `aex`. -/
def LinkOKX6 (E : MethodId → PFact → Node → XFact → Prop) (m : MethodId) (a : PFact) (aex : Excl)
    (M : MethodId) (ic : PFact) : Prop :=
  ∃ (n : Node) (f : XFact) (n' : Node) (c : Call) (e : MicroEdge) (a' : XFact),
    E M ic n f ∧ (M, n, Instr.call c, n') ∈ P.edges ∧ c.callee = m ∧
    e ∈ c.toCallee ∧ a' ∈ (bindX f e).facts ∧ a'.af.fact = a ∧ a'.ex = aex

/-- What a subscription of run 1 means: a caller edge of `M` with the premise `i`, at the call `c`
    with the return node `n'`, binds the annotated fact `a`. -/
def SubOKX6 (E : MethodId → PFact → Node → XFact → Prop) (M : MethodId) (i : PFact) (n' : Node)
    (c : Call) (a : XFact) : Prop :=
  ∃ (n : Node) (f : XFact) (e : MicroEdge),
    E M i n f ∧ (M, n, Instr.call c, n') ∈ P.edges ∧ e ∈ c.toCallee ∧ a ∈ (bindX f e).facts

/-- The invariant of a pipeline object of run 1: what it means in terms of the closure `R`. -/
def InvX6 (R : XObj6 → Prop) : XPObj6 → Prop
  | .base o => R o
  | .link m a aex M ic => LinkOKX6 P (fun M i n f => R (.edge M i n f)) m a aex M ic
  | .sub M i n' c a => SubOKX6 P (fun M i n f => R (.edge M i n f)) M i n' c a
  | .pub m j g => R (.init m j) ∧ R (.edge m j (P.exit m) g)

/-- The invariant of `sysD6X`. -/
abbrev InvD6X : XPObj6 → Prop := InvX6 P (D6X P taint counted L α sinks roots)

variable {P taint counted L α sinks roots}

theorem ruleX6_ne {ps : List XPObj6} {c : XPObj6} (h : RuleX6 P taint counted L α sinks ps c) :
    ps ≠ [] := by
  cases h <;> exact List.cons_ne_nil _ _

theorem ruleX6_local {ps : List XPObj6} {c : XPObj6} (h : RuleX6 P taint counted L α sinks ps c) :
    ∀ p ∈ ps, ∀ q ∈ ps, p.owner = q.owner := by
  cases h with
  | pub => exact local_two _ rfl
  | answer => exact local_two _ rfl
  | reqUp => exact local_two _ rfl
  | start => exact local_one _
  | step => exact local_one _
  | reqStmt => exact local_one _
  | pass => exact local_one _
  | link => exact local_one _
  | added => exact local_one _
  | initA => exact local_one _
  | sub => exact local_one _
  | reqSink => exact local_one _
  | vuln => exact local_one _
  | clean => exact local_one _
  | reqClean => exact local_one _
  | filt => exact local_one _

theorem joinX6_shape {ss : List XPObj6} {p c : XPObj6} (h : JoinX6 counted L ss p c) :
    ss ≠ [] ∧ (∀ s ∈ ss, s.isSub = true ∧ s.topic = p.topic) ∧ p.isPub = true ∧
      (∀ s ∈ ss, ∀ s' ∈ ss, s.owner = s'.owner) := by
  cases h
  refine ⟨List.cons_ne_nil _ _, ?_, rfl, local_one _⟩
  intro s hs
  rw [mem_one hs]
  exact ⟨rfl, rfl⟩

/-- `sysD6X` is well formed (`Pipeline.Sys.WF`): every local rule has at least one premise, all of
    one owner (`answer`, `reqUp` and `pub` have two premises of one method); the join has one
    subscription, of the topic of its publication. -/
theorem sysD6X_wf : (sysD6X P taint counted L α sinks roots).WF where
  rule_ne := fun _ _ h => ruleX6_ne h
  rule_local := fun _ _ h => ruleX6_local h
  join_ne := fun _ _ _ h => (joinX6_shape h).1
  join_sub := fun _ _ _ h => (joinX6_shape h).2.1
  join_pub := fun _ _ _ h => (joinX6_shape h).2.2.1
  join_owner := fun _ _ _ h => (joinX6_shape h).2.2.2

#print axioms sysD6X_wf

/-- The local rules preserve the invariant of `sysD6X`. -/
theorem ruleX6_sound {ps : List XPObj6} {c : XPObj6} (h : RuleX6 P taint counted L α sinks ps c)
    (hps : ∀ p ∈ ps, InvD6X P taint counted L α sinks roots p) :
    InvD6X P taint counted L α sinks roots c := by
  cases h with
  | start => exact D6X.start (fst_of hps :)
  | step he hf => exact D6X.step (fst_of hps :) he hf
  | reqStmt he ht => exact D6X.reqStmt (fst_of hps :) he ht
  | pass he hm => exact D6X.pass (fst_of hps :) he hm
  | link he he1 ha => exact ⟨_, _, _, _, _, _, (fst_of hps :), he, rfl, he1, ha, rfl, rfl⟩
  | added =>
    obtain ⟨_, _, _, _, _, _, hf, he, rfl, he1, ha, rfl, rfl⟩ := fst_of hps
    exact D6X.added hf he he1 ha
  | initA => exact D6X.initA (fst_of hps :)
  | sub he he1 ha => exact ⟨_, _, _, (fst_of hps :), he, he1, ha⟩
  | pub => exact ⟨(fst_of hps :), (snd_of hps :)⟩
  | reqSink hs hc => exact D6X.reqSink (fst_of hps :) hs hc
  | answer hm hov => exact D6X.answer (fst_of hps :) (snd_of hps :) hm hov
  | reqUp hcl hov =>
    obtain ⟨_, _, _, _, _, _, hf, he, hc, he1, ha, rfl, rfl⟩ := snd_of hps
    exact D6X.reqUp (fst_of hps :) hf he hc he1 ha hcl hov
  | vuln hs hc => exact D6X.vuln (fst_of hps :) hs hc
  | clean he hf => exact D6X.clean (fst_of hps :) he hf
  | reqClean he ht => exact D6X.reqClean (fst_of hps :) he ht
  | filt he hp => exact D6X.filt (fst_of hps :) he hp

#print axioms ruleX6_sound

/-- The join preserves the invariant of `sysD6X`. -/
theorem joinX6_sound {ss : List XPObj6} {p c : XPObj6} (h : JoinX6 counted L ss p c)
    (hss : ∀ s ∈ ss, InvD6X P taint counted L α sinks roots s)
    (hp : InvD6X P taint counted L α sinks roots p) :
    InvD6X P taint counted L α sinks roots c := by
  cases h with
  | ret hap hr he2 hr' =>
    obtain ⟨_, _, _, hf, he, he1, ha⟩ := (fst_of hss :)
    obtain ⟨hj, hg⟩ := hp
    exact D6X.ret hf he he1 ha hj hap hg hr he2 hr'

#print axioms joinX6_sound

/-- Soundness: every object of the pipeline closure satisfies its invariant. -/
theorem inv_of_clD6X {x : XPObj6} (h : Cl (sysD6X P taint counted L α sinks roots) x) :
    InvD6X P taint counted L α sinks roots x := by
  induction h with
  | root hx =>
    obtain ⟨M, hM, rfl⟩ := mem_rootsX6 hx
    exact D6X.root hM
  | rule hr _ ih => exact ruleX6_sound hr ih
  | join hj _ _ ihs ihp => exact joinX6_sound hj ihs ihp

#print axioms inv_of_clD6X

/-- Completeness: every object of `D6X` is in the pipeline closure. -/
theorem cl_of_D6X {o : XObj6} (h : D6X P taint counted L α sinks roots o) :
    Cl (sysD6X P taint counted L α sinks roots) (.base o) := by
  induction h with
  | root hM => exact Cl.root (root_mem_rootsX6 hM)
  | start _ ih => exact Cl.rule RuleX6.start (all_one ih)
  | step _ he hf ih => exact Cl.rule (RuleX6.step he hf) (all_one ih)
  | reqStmt _ he ht ih => exact Cl.rule (RuleX6.reqStmt he ht) (all_one ih)
  | pass _ he hm ih => exact Cl.rule (RuleX6.pass he hm) (all_one ih)
  | added _ he he1 ha ih =>
    exact Cl.rule RuleX6.added (all_one (Cl.rule (RuleX6.link he he1 ha) (all_one ih)))
  | initA _ ih => exact Cl.rule RuleX6.initA (all_one ih)
  | ret _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    exact Cl.join (JoinX6.ret hap hr he2 hr')
      (all_one (Cl.rule (RuleX6.sub he he1 ha) (all_one ihf)))
      (Cl.rule RuleX6.pub (all_two ihj ihg))
  | reqSink _ hs hc ih => exact Cl.rule (RuleX6.reqSink hs hc) (all_one ih)
  | answer _ _ hm hov ihr iha => exact Cl.rule (RuleX6.answer hm hov) (all_two ihr iha)
  | reqUp _ _ he hc he1 ha hcl hov ihr ihf =>
    subst hc
    exact Cl.rule (RuleX6.reqUp hcl hov)
      (all_two ihr (Cl.rule (RuleX6.link he he1 ha) (all_one ihf)))
  | vuln _ hs hc ih => exact Cl.rule (RuleX6.vuln hs hc) (all_one ih)
  | clean _ he hf ih => exact Cl.rule (RuleX6.clean he hf) (all_one ih)
  | reqClean _ he ht ih => exact Cl.rule (RuleX6.reqClean he ht) (all_one ih)
  | filt _ he hp ih => exact Cl.rule (RuleX6.filt he hp) (all_one ih)

#print axioms cl_of_D6X

/-- THE THEOREM for run 1 with the exclusion: the pipeline closure on the closure objects is
    exactly `D6X` (with the annotated facts). -/
theorem clD6X_iff {o : XObj6} :
    Cl (sysD6X P taint counted L α sinks roots) (.base o) ↔ D6X P taint counted L α sinks roots o :=
  ⟨fun h => inv_of_clD6X h, cl_of_D6X⟩

#print axioms clD6X_iff

/-- A link of `sysD6X` is exactly a binding of a caller edge of `D6X`: the path fact of the bound
    fact and its exclusion. -/
theorem clD6X_link {m : MethodId} {a : PFact} {aex : Excl} {M : MethodId} {ic : PFact} :
    Cl (sysD6X P taint counted L α sinks roots) (.link m a aex M ic) ↔
      LinkOKX6 P (fun M i n f => D6X P taint counted L α sinks roots (.edge M i n f))
        m a aex M ic := by
  refine ⟨fun h => inv_of_clD6X h, ?_⟩
  rintro ⟨_, _, _, _, _, _, hf, he, rfl, he1, ha, rfl, rfl⟩
  exact Cl.rule (RuleX6.link he he1 ha) (all_one (cl_of_D6X hf))

#print axioms clD6X_link

/-- A subscription of `sysD6X` is exactly an annotated binding of a caller edge of `D6X` at a
    call. -/
theorem clD6X_sub {M : MethodId} {i : PFact} {n' : Node} {c : Call} {a : XFact} :
    Cl (sysD6X P taint counted L α sinks roots) (.sub M i n' c a) ↔
      SubOKX6 P (fun M i n f => D6X P taint counted L α sinks roots (.edge M i n f)) M i n' c a := by
  refine ⟨fun h => inv_of_clD6X h, ?_⟩
  rintro ⟨_, _, _, hf, he, he1, ha⟩
  exact Cl.rule (RuleX6.sub he he1 ha) (all_one (cl_of_D6X hf))

#print axioms clD6X_sub

/-- A publication of `sysD6X` is exactly an initial fact of `D6X` with an annotated exit edge of
    it. -/
theorem clD6X_pub {m : MethodId} {j : PFact} {g : XFact} :
    Cl (sysD6X P taint counted L α sinks roots) (.pub m j g) ↔
      D6X P taint counted L α sinks roots (.init m j) ∧
        D6X P taint counted L α sinks roots (.edge m j (P.exit m) g) := by
  refine ⟨fun h => inv_of_clD6X h, ?_⟩
  rintro ⟨hj, hg⟩
  exact Cl.rule RuleX6.pub (all_two (cl_of_D6X hj) (cl_of_D6X hg))

#print axioms clD6X_pub

end SysD6X

/-! ## 2. The restricted forward run with must-premises and exclusions: the closure `DRX` -/

/-- The method of an object of `DRX`. -/
def xobjOwner : XObj → MethodId
  | .init M _ _ _ => M
  | .edge M _ _ _ _ _ => M
  | .added M _ _ _ => M
  | .req M _ _ => M
  | .vuln M _ _ _ => M

/-- The pipeline objects of `DRX` (the objects `XObj` carry the must flags and the exclusions). -/
inductive XPObj where
  /-- an object of `DRX`; owner: its method -/
  | base (o : XObj)
  /-- the callee `m` holds the link: the added fact `a` with its flag `am` (`[any-taint]`) and its
      exclusion `aex`, from a caller edge of `M` with the premise `ic` -/
  | link (m : MethodId) (a : PFact) (am : Bool) (aex : Excl) (M : MethodId) (ic : PFact)
  /-- the caller's subscription: caller premise `(i, mi, iex)`, return node `n'`, call `c`,
      annotated bound fact `a` -/
  | sub  (M : MethodId) (i : PFact) (mi : Bool) (iex : Excl) (n' : Node) (c : Call) (a : XFact)
  /-- a published summary edge `(j, mj, jex) → g` of `m` (`g` annotated) -/
  | pub  (m : MethodId) (j : PFact) (mj : Bool) (jex : Excl) (g : XFact)
deriving DecidableEq

/-- The owner of a pipeline object of `DRX`. -/
def XPObj.owner : XPObj → MethodId
  | .base o => xobjOwner o
  | .link m _ _ _ _ _ => m
  | .sub M _ _ _ _ _ _ => M
  | .pub m _ _ _ _ => m

def XPObj.isSub : XPObj → Bool
  | .sub .. => true
  | _ => false

def XPObj.isPub : XPObj → Bool
  | .pub .. => true
  | _ => false

/-- The topic: the callee of a subscription, the publisher of a publication (and the owner for
    the other objects, which never meet a topic). -/
def XPObj.topic : XPObj → MethodId
  | .base o => xobjOwner o
  | .link m _ _ _ _ _ => m
  | .sub _ _ _ _ _ c _ => c.callee
  | .pub m _ _ _ _ => m

/-- The roots of a restricted run: the zero fact of each root method, not a must-premise, with no
    exclusion. -/
def rootsX (roots : List MethodId) : List XPObj :=
  roots.map (fun M => .base (.init M zeroFact false Excl.empty))

theorem mem_rootsX {roots : List MethodId} {x : XPObj} (h : x ∈ rootsX roots) :
    ∃ M, M ∈ roots ∧ x = .base (.init M zeroFact false Excl.empty) := by
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1 h
  exact ⟨M, hM, rfl⟩

theorem root_mem_rootsX {roots : List MethodId} {M : MethodId} (h : M ∈ roots) :
    (.base (.init M zeroFact false Excl.empty) : XPObj) ∈ rootsX roots :=
  List.mem_map.2 ⟨M, h, rfl⟩

section SysDRX
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Excl → Option (PFact × Excl))
  (sat : PFact → Excl → PFact → Excl → Bool)
  (restrict : PFact → Excl → XFact → DemandEdge → Option XFact)
  (recs : MethodId → PFact × Bool × Excl × XFact → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- The local rules of `DRX`. -/
inductive RuleRX : List XPObj → XPObj → Prop where
  | start {M j mj jex} :
      RuleRX [.base (.init M j mj jex)] (.base (.edge M j mj jex (P.entry M) (startX j mj jex)))
  | step {M i mi iex n f n' s f'} : (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transferX taint counted L s f).facts →
      RuleRX [.base (.edge M i mi iex n f)] (.base (.edge M i mi iex n' f'))
  | reqStmt {M i mi iex n f n' s t} : (M, n, Instr.stmt s, n') ∈ P.edges →
      t ∈ (transferX taint counted L s f).reqs →
      RuleRX [.base (.edge M i mi iex n f)] (.base (.req M i t))
  | pass {M i mi iex n f n' c} : (M, n, Instr.call c, n') ∈ P.edges →
      memB f.af.fact.base c.touched = false →
      RuleRX [.base (.edge M i mi iex n f)] (.base (.edge M i mi iex n' f))
  /-- the caller sends the link to the callee (a message): the added fact with its flag and its
      exclusion -/
  | link {M i mi iex n f n' c e a} : (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (bindX f e).facts →
      RuleRX [.base (.edge M i mi iex n f)]
        (.link c.callee a.af.fact (a.af.fact.kind.isAny && !a.af.demand) a.ex M i)
  /-- the callee stores the added fact of a link, with its flag and its exclusion -/
  | added {m a am aex M ic} : RuleRX [.link m a am aex M ic] (.base (.added m a am aex))
  /-- the emission with the must flag and the exclusion (decision 8, DESIGN A2) -/
  | initR {m a am aex d j mj jex} : demand m d → emitTX emit d.din a am aex = some (j, mj, jex) →
      RuleRX [.base (.added m a am aex)] (.base (.init m j mj jex))
  /-- the caller subscribes at the call, with its premise (flag, exclusion) and the annotated
      bound fact -/
  | sub {M i mi iex n f n' c e a} : (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (bindX f e).facts →
      RuleRX [.base (.edge M i mi iex n f)] (.sub M i mi iex n' c a)
  /-- the callee restricts a summary edge by one of its demand edges and publishes the result,
      with the must flag and the exclusion of its premise -/
  | pub {m j mj jex g d g'} : demand m d → restrict j jex g d = some g' →
      RuleRX [.base (.init m j mj jex), .base (.edge m j mj jex (P.exit m) g)] (.pub m j mj jex g')
  /-- a persisted record: a fixed predicate, so the rule is local at the caller; a must record
      applied by `applicable` only gives a demand result (`recLayerX`) -/
  | retRec {M i mi iex n f n' c e1 a j mj jex g r e2 r'} : (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (bindX f e1).facts →
      recs c.callee (j, mj, jex, g) →
      (sat j jex a.af.fact a.ex = true ∨ applicable j a.af.fact = true) →
      r ∈ (applySummaryX a j jex g).facts →
      e2 ∈ c.fromCallee → r' ∈ (bindX r e2).facts →
      RuleRX [.base (.edge M i mi iex n f)]
        (.base (.edge M i mi iex n' (limitFX counted L (recLayerX mj (sat j jex a.af.fact a.ex) r'))))
  | reqSink {M i mi iex n f s t} : (M, n, s) ∈ sinks → checkX i f s = .request t →
      RuleRX [.base (.edge M i mi iex n f)] (.base (.req M i t))
  | answer {M i t a am aex} : a.mark = .conc t → overlapX a aex i Excl.empty = true →
      RuleRX [.base (.req M i t), .base (.added M a am aex)]
        (.base (.init M (answerInit i a t) false Excl.empty))
  /-- the callee climbs a request through a link (the conclusion is a message to the caller) -/
  | reqUp {m j t a am aex M ic} : climbsB a.mark t = true → overlapX a aex j Excl.empty = true →
      RuleRX [.base (.req m j t), .link m a am aex M ic] (.base (.req M ic t))
  | vuln {M i mi iex n f s} : (M, n, s) ∈ sinks → checkX i f s = .triggered →
      RuleRX [.base (.edge M i mi iex n f)] (.base (.vuln M n s f.af.demand))
  | clean {M i mi iex n f n' cl f'} : (M, n, Instr.clean cl, n') ∈ P.edges →
      f' ∈ (cleanResX cl f).facts →
      RuleRX [.base (.edge M i mi iex n f)] (.base (.edge M i mi iex n' f'))
  | reqClean {M i mi iex n f n' cl t} : (M, n, Instr.clean cl, n') ∈ P.edges →
      t ∈ (cleanResX cl f).reqs →
      RuleRX [.base (.edge M i mi iex n f)] (.base (.req M i t))
  | filt {M i mi iex n f n' b may} : (M, n, Instr.filt b may, n') ∈ P.edges →
      (f.af.fact.base = b → may f.af.fact.path = true) →
      RuleRX [.base (.edge M i mi iex n f)] (.base (.edge M i mi iex n' f))

/-- The join of `DRX` (the rule `ret`): the subscription of the caller premise `(i, mi, iex)` and
    a publication of the callee premise `(j, mj, jex)`. The join reads `sat j jex a`, the summary
    application with the premise exclusion `jex`, not `mj`. -/
inductive JoinRX : List XPObj → XPObj → XPObj → Prop where
  | ret {M i mi iex n' c a j mj jex g r e2 r'} : sat j jex a.af.fact a.ex = true →
      r ∈ (applySummaryX a j jex g).facts → e2 ∈ c.fromCallee → r' ∈ (bindX r e2).facts →
      JoinRX [.sub M i mi iex n' c a] (.pub c.callee j mj jex g)
        (.base (.edge M i mi iex n' (limitFX counted L r')))

/-- The restricted forward run with must-premises and exclusions as a pipeline system. -/
def sysDRX : Sys XPObj MethodId MethodId where
  owner := XPObj.owner
  roots := rootsX roots
  rule  := RuleRX P taint counted L demand emit sat restrict recs sinks
  isSub := XPObj.isSub
  isPub := XPObj.isPub
  topic := XPObj.topic
  join  := JoinRX counted L sat

/-- What a link means: a caller edge of `M` with the premise `ic` (any must flag, any exclusion),
    at a call of `m`, binds an annotated fact `a'` whose path fact is `a`, whose flag is `am` and
    whose exclusion is `aex`. -/
def LinkOKX (E : MethodId → PFact → Bool → Excl → Node → XFact → Prop) (m : MethodId) (a : PFact)
    (am : Bool) (aex : Excl) (M : MethodId) (ic : PFact) : Prop :=
  ∃ (mc : Bool) (icx : Excl) (n : Node) (f : XFact) (n' : Node) (c : Call) (e : MicroEdge)
    (a' : XFact),
    E M ic mc icx n f ∧ (M, n, Instr.call c, n') ∈ P.edges ∧ c.callee = m ∧
    e ∈ c.toCallee ∧ a' ∈ (bindX f e).facts ∧ a'.af.fact = a ∧
    (a'.af.fact.kind.isAny && !a'.af.demand) = am ∧ a'.ex = aex

/-- What a subscription means: a caller edge of `M` with the premise `(i, mi, iex)`, at the call
    `c` with the return node `n'`, binds the annotated fact `a`. -/
def SubOKX (E : MethodId → PFact → Bool → Excl → Node → XFact → Prop) (M : MethodId) (i : PFact)
    (mi : Bool) (iex : Excl) (n' : Node) (c : Call) (a : XFact) : Prop :=
  ∃ (n : Node) (f : XFact) (e : MicroEdge),
    E M i mi iex n f ∧ (M, n, Instr.call c, n') ∈ P.edges ∧ e ∈ c.toCallee ∧
    a ∈ (bindX f e).facts

/-- What a publication means: a summary edge of the premise `(j, mj, jex)` of `m`, restricted by a
    demand edge of `m`. -/
def PubRX (R : XObj → Prop) (m : MethodId) (j : PFact) (mj : Bool) (jex : Excl) (g' : XFact) :
    Prop :=
  ∃ (g : XFact) (d : DemandEdge), R (.init m j mj jex) ∧ R (.edge m j mj jex (P.exit m) g) ∧
    demand m d ∧ restrict j jex g d = some g'

/-- The invariant of a pipeline object of `DRX`: what it means in terms of the closure `R`. -/
def InvRX (R : XObj → Prop) : XPObj → Prop
  | .base o => R o
  | .link m a am aex M ic =>
    LinkOKX P (fun M i mi iex n f => R (.edge M i mi iex n f)) m a am aex M ic
  | .sub M i mi iex n' c a =>
    SubOKX P (fun M i mi iex n f => R (.edge M i mi iex n f)) M i mi iex n' c a
  | .pub m j mj jex g => PubRX P demand restrict R m j mj jex g

/-- The invariant of `sysDRX`. -/
abbrev InvDRX : XPObj → Prop :=
  InvRX P demand restrict (DRX P taint counted L demand emit sat restrict recs sinks roots)

variable {P taint counted L demand emit sat restrict recs sinks roots}

theorem ruleRX_ne {ps : List XPObj} {c : XPObj}
    (h : RuleRX P taint counted L demand emit sat restrict recs sinks ps c) : ps ≠ [] := by
  cases h <;> exact List.cons_ne_nil _ _

theorem ruleRX_local {ps : List XPObj} {c : XPObj}
    (h : RuleRX P taint counted L demand emit sat restrict recs sinks ps c) :
    ∀ p ∈ ps, ∀ q ∈ ps, p.owner = q.owner := by
  cases h with
  | pub => exact local_two _ rfl
  | answer => exact local_two _ rfl
  | reqUp => exact local_two _ rfl
  | start => exact local_one _
  | step => exact local_one _
  | reqStmt => exact local_one _
  | pass => exact local_one _
  | link => exact local_one _
  | added => exact local_one _
  | initR => exact local_one _
  | sub => exact local_one _
  | retRec => exact local_one _
  | reqSink => exact local_one _
  | vuln => exact local_one _
  | clean => exact local_one _
  | reqClean => exact local_one _
  | filt => exact local_one _

theorem joinRX_shape {ss : List XPObj} {p c : XPObj} (h : JoinRX counted L sat ss p c) :
    ss ≠ [] ∧ (∀ s ∈ ss, s.isSub = true ∧ s.topic = p.topic) ∧ p.isPub = true ∧
      (∀ s ∈ ss, ∀ s' ∈ ss, s.owner = s'.owner) := by
  cases h
  refine ⟨List.cons_ne_nil _ _, ?_, rfl, local_one _⟩
  intro s hs
  rw [mem_one hs]
  exact ⟨rfl, rfl⟩

/-- `sysDRX` is well formed (`Pipeline.Sys.WF`): every local rule has at least one premise, all of
    one owner (`answer`, `reqUp` and `pub` have two premises of one method); the join has one
    subscription, of the topic of its publication. -/
theorem sysDRX_wf :
    (sysDRX P taint counted L demand emit sat restrict recs sinks roots).WF where
  rule_ne := fun _ _ h => ruleRX_ne h
  rule_local := fun _ _ h => ruleRX_local h
  join_ne := fun _ _ _ h => (joinRX_shape h).1
  join_sub := fun _ _ _ h => (joinRX_shape h).2.1
  join_pub := fun _ _ _ h => (joinRX_shape h).2.2.1
  join_owner := fun _ _ _ h => (joinRX_shape h).2.2.2

#print axioms sysDRX_wf

/-- The local rules preserve the invariant of `sysDRX`. -/
theorem ruleRX_sound {ps : List XPObj} {c : XPObj}
    (h : RuleRX P taint counted L demand emit sat restrict recs sinks ps c)
    (hps : ∀ p ∈ ps, InvDRX P taint counted L demand emit sat restrict recs sinks roots p) :
    InvDRX P taint counted L demand emit sat restrict recs sinks roots c := by
  cases h with
  | start => exact DRX.start (fst_of hps :)
  | step he hf => exact DRX.step (fst_of hps :) he hf
  | reqStmt he ht => exact DRX.reqStmt (fst_of hps :) he ht
  | pass he hm => exact DRX.pass (fst_of hps :) he hm
  | link he he1 ha =>
    exact ⟨_, _, _, _, _, _, _, _, (fst_of hps :), he, rfl, he1, ha, rfl, rfl, rfl⟩
  | added =>
    obtain ⟨_, _, _, _, _, _, _, _, hf, he, rfl, he1, ha, rfl, rfl, rfl⟩ := fst_of hps
    exact DRX.added hf he he1 ha
  | initR hd he => exact DRX.initR (fst_of hps :) hd he
  | sub he he1 ha => exact ⟨_, _, _, (fst_of hps :), he, he1, ha⟩
  | pub hd hres => exact ⟨_, _, (fst_of hps :), (snd_of hps :), hd, hres⟩
  | retRec he he1 ha hrec hs hr he2 hr' =>
    exact DRX.retRec (fst_of hps :) he he1 ha hrec hs hr he2 hr'
  | reqSink hs hc => exact DRX.reqSink (fst_of hps :) hs hc
  | answer hm hov => exact DRX.answer (fst_of hps :) (snd_of hps :) hm hov
  | reqUp hcl hov =>
    obtain ⟨_, _, _, _, _, _, _, _, hf, he, hc, he1, ha, rfl, _, rfl⟩ := snd_of hps
    exact DRX.reqUp (fst_of hps :) hf he hc he1 ha hcl hov
  | vuln hs hc => exact DRX.vuln (fst_of hps :) hs hc
  | clean he hf => exact DRX.clean (fst_of hps :) he hf
  | reqClean he ht => exact DRX.reqClean (fst_of hps :) he ht
  | filt he hp => exact DRX.filt (fst_of hps :) he hp

#print axioms ruleRX_sound

/-- The join preserves the invariant of `sysDRX`. -/
theorem joinRX_sound {ss : List XPObj} {p c : XPObj} (h : JoinRX counted L sat ss p c)
    (hss : ∀ s ∈ ss, InvDRX P taint counted L demand emit sat restrict recs sinks roots s)
    (hp : InvDRX P taint counted L demand emit sat restrict recs sinks roots p) :
    InvDRX P taint counted L demand emit sat restrict recs sinks roots c := by
  cases h with
  | ret hs hr he2 hr' =>
    obtain ⟨_, _, _, hf, he, he1, ha⟩ := (fst_of hss :)
    obtain ⟨_, _, hj, hg, hd, hres⟩ := hp
    exact DRX.ret hf he he1 ha hj hg hd hres hs hr he2 hr'

#print axioms joinRX_sound

/-- Soundness: every object of the pipeline closure satisfies its invariant. -/
theorem inv_of_clDRX {x : XPObj}
    (h : Cl (sysDRX P taint counted L demand emit sat restrict recs sinks roots) x) :
    InvDRX P taint counted L demand emit sat restrict recs sinks roots x := by
  induction h with
  | root hx =>
    obtain ⟨M, hM, rfl⟩ := mem_rootsX hx
    exact DRX.root hM
  | rule hr _ ih => exact ruleRX_sound hr ih
  | join hj _ _ ihs ihp => exact joinRX_sound hj ihs ihp

#print axioms inv_of_clDRX

/-- Completeness: every object of `DRX` is in the pipeline closure. -/
theorem cl_of_DRX {o : XObj} (h : DRX P taint counted L demand emit sat restrict recs sinks roots o) :
    Cl (sysDRX P taint counted L demand emit sat restrict recs sinks roots) (.base o) := by
  induction h with
  | root hM => exact Cl.root (root_mem_rootsX hM)
  | start _ ih => exact Cl.rule RuleRX.start (all_one ih)
  | step _ he hf ih => exact Cl.rule (RuleRX.step he hf) (all_one ih)
  | reqStmt _ he ht ih => exact Cl.rule (RuleRX.reqStmt he ht) (all_one ih)
  | pass _ he hm ih => exact Cl.rule (RuleRX.pass he hm) (all_one ih)
  | added _ he he1 ha ih =>
    exact Cl.rule RuleRX.added (all_one (Cl.rule (RuleRX.link he he1 ha) (all_one ih)))
  | initR _ hd he ih => exact Cl.rule (RuleRX.initR hd he) (all_one ih)
  | ret _ he he1 ha _ _ hd hres hs hr he2 hr' ihf ihj ihg =>
    exact Cl.join (JoinRX.ret hs hr he2 hr')
      (all_one (Cl.rule (RuleRX.sub he he1 ha) (all_one ihf)))
      (Cl.rule (RuleRX.pub hd hres) (all_two ihj ihg))
  | retRec _ he he1 ha hrec hs hr he2 hr' ih =>
    exact Cl.rule (RuleRX.retRec he he1 ha hrec hs hr he2 hr') (all_one ih)
  | reqSink _ hs hc ih => exact Cl.rule (RuleRX.reqSink hs hc) (all_one ih)
  | answer _ _ hm hov ihr iha => exact Cl.rule (RuleRX.answer hm hov) (all_two ihr iha)
  | reqUp _ _ he hc he1 ha hcl hov ihr ihf =>
    subst hc
    exact Cl.rule (RuleRX.reqUp hcl hov)
      (all_two ihr (Cl.rule (RuleRX.link he he1 ha) (all_one ihf)))
  | vuln _ hs hc ih => exact Cl.rule (RuleRX.vuln hs hc) (all_one ih)
  | clean _ he hf ih => exact Cl.rule (RuleRX.clean he hf) (all_one ih)
  | reqClean _ he ht ih => exact Cl.rule (RuleRX.reqClean he ht) (all_one ih)
  | filt _ he hp ih => exact Cl.rule (RuleRX.filt he hp) (all_one ih)

#print axioms cl_of_DRX

/-- THE THEOREM for the restricted forward run with must-premises and exclusions: the pipeline
    closure on the closure objects is exactly `DRX` (with the must flags and the exclusions of the
    premises, the flags and the exclusions of the added facts, and the annotated conclusions). -/
theorem clDRX_iff {o : XObj} :
    Cl (sysDRX P taint counted L demand emit sat restrict recs sinks roots) (.base o) ↔
      DRX P taint counted L demand emit sat restrict recs sinks roots o :=
  ⟨fun h => inv_of_clDRX h, cl_of_DRX⟩

#print axioms clDRX_iff

/-- A link of `sysDRX` is exactly a binding of a caller edge of `DRX` (with any must flag and any
    exclusion of the caller premise), with the flag `am` and the exclusion `aex` of the bound
    fact. -/
theorem clDRX_link {m : MethodId} {a : PFact} {am : Bool} {aex : Excl} {M : MethodId}
    {ic : PFact} :
    Cl (sysDRX P taint counted L demand emit sat restrict recs sinks roots)
        (.link m a am aex M ic) ↔
      LinkOKX P (fun M i mi iex n f => DRX P taint counted L demand emit sat restrict recs sinks
        roots (.edge M i mi iex n f)) m a am aex M ic := by
  refine ⟨fun h => inv_of_clDRX h, ?_⟩
  rintro ⟨_, _, _, _, _, _, _, _, hf, he, rfl, he1, ha, rfl, rfl, rfl⟩
  exact Cl.rule (RuleRX.link he he1 ha) (all_one (cl_of_DRX hf))

#print axioms clDRX_link

/-- A subscription of `sysDRX` is exactly an annotated binding of a caller edge of `DRX` at a
    call, with the must flag and the exclusion of the caller premise. -/
theorem clDRX_sub {M : MethodId} {i : PFact} {mi : Bool} {iex : Excl} {n' : Node} {c : Call}
    {a : XFact} :
    Cl (sysDRX P taint counted L demand emit sat restrict recs sinks roots)
        (.sub M i mi iex n' c a) ↔
      SubOKX P (fun M i mi iex n f => DRX P taint counted L demand emit sat restrict recs sinks
        roots (.edge M i mi iex n f)) M i mi iex n' c a := by
  refine ⟨fun h => inv_of_clDRX h, ?_⟩
  rintro ⟨_, _, _, hf, he, he1, ha⟩
  exact Cl.rule (RuleRX.sub he he1 ha) (all_one (cl_of_DRX hf))

#print axioms clDRX_sub

/-- A publication of `sysDRX` is exactly a summary edge of a premise `(j, mj, jex)` of `DRX`,
    restricted by a demand edge of its method. -/
theorem clDRX_pub {m : MethodId} {j : PFact} {mj : Bool} {jex : Excl} {g' : XFact} :
    Cl (sysDRX P taint counted L demand emit sat restrict recs sinks roots) (.pub m j mj jex g') ↔
      ∃ (g : XFact) (d : DemandEdge),
        DRX P taint counted L demand emit sat restrict recs sinks roots (.init m j mj jex) ∧
        DRX P taint counted L demand emit sat restrict recs sinks roots
          (.edge m j mj jex (P.exit m) g) ∧
        demand m d ∧ restrict j jex g d = some g' := by
  refine ⟨fun h => inv_of_clDRX h, ?_⟩
  rintro ⟨_, _, hj, hg, hd, hres⟩
  exact Cl.rule (RuleRX.pub hd hres) (all_two (cl_of_DRX hj) (cl_of_DRX hg))

#print axioms clDRX_pub

end SysDRX

/-! ## 3. The pipeline theorems for `sysD6X` and `sysDRX`

  The theorems of `PipelineProofs.lean` are generic over the system (`Pipeline.Sys`), so they
  apply to the two encodings with `sysD6X_wf` and `sysDRX_wf`. -/

/-- What the driver reads from the final state of run 1 with the exclusion: the closure objects
    that it holds. -/
def resultX6 (st : St XPObj6 MethodId MethodId) : XObj6 → Prop := fun o => XPObj6.base o ∈ st.known

/-- What the driver reads from the final state of a restricted run with the exclusion: the closure
    objects that it holds. -/
def resultX (st : St XPObj MethodId MethodId) : XObj → Prop := fun o => XPObj.base o ∈ st.known

section Instances
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}

section RunD6X
variable {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId} {st : St XPObj6 MethodId MethodId}

/-- Soundness of a run of `sysD6X` (`Pipeline.reach_sound`): at every reachable state (quiescent
    or not), every processed closure object is an object of `D6X`. -/
theorem known_D6X (hR : Pipeline.Reach (sysD6X P taint counted L α sinks roots) st) {o : XObj6}
    (h : XPObj6.base o ∈ st.known) : D6X P taint counted L α sinks roots o :=
  inv_of_clD6X ((reach_sound hR).known _ h)

#print axioms known_D6X

/-- A COMPLETE RUN 1 WITH THE EXCLUSION (`Pipeline.quiescent_exact`): at a reachable quiescent
    state the driver reads exactly `D6X` (the annotated edges with their exclusions included). -/
theorem result_D6X (hR : Pipeline.Reach (sysD6X P taint counted L α sinks roots) st)
    (hQ : st.Quiescent) : resultX6 st = D6X P taint counted L α sinks roots := by
  funext o
  exact propext ((quiescent_exact sysD6X_wf hR hQ).trans clD6X_iff)

#print axioms result_D6X

/-- The summary edge is never lost in run 1 with the exclusion (`Pipeline.no_lost_join`): at a
    reachable quiescent state, a processed subscription (with the annotated bound fact `a`) and a
    processed publication (with the annotated exit fact `g`) that satisfy the condition of
    `D6X.ret` have their caller edge processed. -/
theorem no_lost_summary_D6X (hR : Pipeline.Reach (sysD6X P taint counted L α sinks roots) st)
    (hQ : st.Quiescent) {M : MethodId} {i : PFact} {n' : Node} {c : Call} {a : XFact}
    {j : PFact} {g r : XFact} {e2 : MicroEdge} {r' : XFact}
    (hs : XPObj6.sub M i n' c a ∈ st.known) (hp : XPObj6.pub c.callee j g ∈ st.known)
    (hap : applicable j a.af.fact = true) (hr : r ∈ (applySummaryX a j Excl.empty g).facts)
    (he2 : e2 ∈ c.fromCallee) (hr' : r' ∈ (bindX r e2).facts) :
    XPObj6.base (.edge M i n' (limitFX counted L r')) ∈ st.known :=
  no_lost_join sysD6X_wf hR hQ (JoinX6.ret hap hr he2 hr') (all_one hs) hp

#print axioms no_lost_summary_D6X

end RunD6X

section RunDRX
variable {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Excl → Option (PFact × Excl)}
  {sat : PFact → Excl → PFact → Excl → Bool}
  {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
  {recs : MethodId → PFact × Bool × Excl × XFact → Prop} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId} {st : St XPObj MethodId MethodId}

/-- Soundness of a run of `sysDRX` (`Pipeline.reach_sound`): at every reachable state (quiescent
    or not), every processed closure object is an object of `DRX`, with its must flags and its
    exclusions. -/
theorem known_DRX
    (hR : Pipeline.Reach (sysDRX P taint counted L demand emit sat restrict recs sinks roots) st)
    {o : XObj} (h : XPObj.base o ∈ st.known) :
    DRX P taint counted L demand emit sat restrict recs sinks roots o :=
  inv_of_clDRX ((reach_sound hR).known _ h)

#print axioms known_DRX

/-- A COMPLETE RESTRICTED FORWARD RUN WITH MUST-PREMISES AND EXCLUSIONS
    (`Pipeline.quiescent_exact`): at a reachable quiescent state the driver reads exactly `DRX`
    (the initial facts and the edges with their must flags and exclusions, the added facts with
    their flags and exclusions, the requests and the vulnerabilities). So every theorem on `DRX`
    holds for the result of the analyzer. -/
theorem result_DRX
    (hR : Pipeline.Reach (sysDRX P taint counted L demand emit sat restrict recs sinks roots) st)
    (hQ : st.Quiescent) :
    resultX st = DRX P taint counted L demand emit sat restrict recs sinks roots := by
  funext o
  exact propext ((quiescent_exact sysDRX_wf hR hQ).trans clDRX_iff)

#print axioms result_DRX

/-- The summary edge is never lost in a restricted forward run with must-premises and exclusions
    (`Pipeline.no_lost_join`): at a reachable quiescent state, a processed subscription of the
    caller premise `(i, mi, iex)` and a processed publication of the callee premise `(j, mj, jex)`
    with `sat j jex a.af.fact a.ex` have their caller edge of the premise `(i, mi, iex)`
    processed. -/
theorem no_lost_summary_DRX
    (hR : Pipeline.Reach (sysDRX P taint counted L demand emit sat restrict recs sinks roots) st)
    (hQ : st.Quiescent) {M : MethodId} {i : PFact} {mi : Bool} {iex : Excl} {n' : Node} {c : Call}
    {a : XFact} {j : PFact} {mj : Bool} {jex : Excl} {g r : XFact} {e2 : MicroEdge} {r' : XFact}
    (hs : XPObj.sub M i mi iex n' c a ∈ st.known) (hp : XPObj.pub c.callee j mj jex g ∈ st.known)
    (hsat : sat j jex a.af.fact a.ex = true) (hr : r ∈ (applySummaryX a j jex g).facts)
    (he2 : e2 ∈ c.fromCallee) (hr' : r' ∈ (bindX r e2).facts) :
    XPObj.base (.edge M i mi iex n' (limitFX counted L r')) ∈ st.known :=
  no_lost_join sysDRX_wf hR hQ (JoinRX.ret hsat hr he2 hr') (all_one hs) hp

#print axioms no_lost_summary_DRX

end RunDRX

section RunDRXs
variable {demand : MethodId → DemandEdge → Prop}
  {recs : MethodId → PFact × Bool × Excl × XFact → Prop} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId} {st : St XPObj MethodId MethodId}

/-- The spec instance (`emitX`, `satX`, `restrictX`): at a reachable quiescent state of `sysDRX`
    with the spec operations the driver reads exactly `DRXs`. -/
theorem result_DRXs
    (hR : Pipeline.Reach (sysDRX P taint counted L demand emitX satX restrictX recs sinks roots) st)
    (hQ : st.Quiescent) : resultX st = DRXs P taint counted L demand recs sinks roots :=
  result_DRX hR hQ

#print axioms result_DRXs

end RunDRXs
end Instances

/-! ## 4. Sanity: a normal `[any-taint]/{name}` edge in the pipeline closures

  The program `0: (source) → 1: this.name = v → 2` of method `0`: the source of
  `AnyTaint.Sanity` gives the normal `(this, [], [any-taint], {}, T)` at node `1`; the strong
  write (the setter vector `AnyTaintEx.Vec.setter`) gives the NORMAL `(this, [], [any-taint],
  {name}, T)` (`Vec.cAnn`) at node `2`. It is an object of both encoded systems, so the encodings
  are not vacuous on the exclusion. -/

namespace SanityX

/-- Method `0`: the source statement from node `0` to `1`, the setter from node `1` to `2`. -/
def P : Program :=
  ⟨fun _ => 0, fun _ => 2,
   [(0, 0, .stmt AnyTaint.Sanity.s, 1), (0, 1, .stmt AnyTaintEx.Vec.setter, 2)]⟩

theorem mem_src : ((0 : MethodId), (0 : Node), Instr.stmt AnyTaint.Sanity.s, (1 : Node)) ∈ P.edges :=
  List.mem_cons_self

theorem mem_setter :
    ((0 : MethodId), (1 : Node), Instr.stmt AnyTaintEx.Vec.setter, (2 : Node)) ∈ P.edges :=
  List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)

/-- The source gives the normal `[any-taint]` with no exclusion (`Vec.cIn`). -/
theorem src_cIn :
    AnyTaintEx.Vec.cIn ∈ (transferX AnyTaint.Sanity.taintSrc AnyTaintEx.Vec.cnt 3 AnyTaint.Sanity.s
      (startX zeroFact false Excl.empty)).facts := by decide

/-- The strong write gives the normal `[any-taint]/{name}` (`Vec.cAnn`). -/
theorem setter_cAnn :
    AnyTaintEx.Vec.cAnn ∈ (transferX AnyTaint.Sanity.taintSrc AnyTaintEx.Vec.cnt 3
      AnyTaintEx.Vec.setter AnyTaintEx.Vec.cIn).facts := by decide

/-- Run 1: the normal `[any-taint]/{name}` edge is an object of `D6X`. -/
theorem d6x_ann :
    D6X P AnyTaint.Sanity.taintSrc AnyTaintEx.Vec.cnt 3 policy1 [] [0]
      (.edge 0 zeroFact 2 AnyTaintEx.Vec.cAnn) :=
  D6X.step (D6X.step (D6X.start (D6X.root (List.mem_singleton.mpr rfl))) mem_src src_cIn)
    mem_setter setter_cAnn

#print axioms d6x_ann

/-- A restricted run: the normal `[any-taint]/{name}` edge is an object of `DRXs`. -/
theorem drx_ann :
    DRXs P AnyTaint.Sanity.taintSrc AnyTaintEx.Vec.cnt 3 (fun _ _ => False) (fun _ _ => False) []
      [0] (.edge 0 zeroFact false Excl.empty 2 AnyTaintEx.Vec.cAnn) :=
  DRX.step (DRX.step (DRX.start (DRX.root (List.mem_singleton.mpr rfl))) mem_src src_cIn)
    mem_setter setter_cAnn

#print axioms drx_ann

example : Cl (sysD6X P AnyTaint.Sanity.taintSrc AnyTaintEx.Vec.cnt 3 policy1 [] [0])
    (.base (.edge 0 zeroFact 2 AnyTaintEx.Vec.cAnn)) :=
  cl_of_D6X d6x_ann

example : Cl (sysDRX P AnyTaint.Sanity.taintSrc AnyTaintEx.Vec.cnt 3 (fun _ _ => False) emitX satX
    restrictX (fun _ _ => False) [] [0]) (.base (.edge 0 zeroFact false Excl.empty 2
      AnyTaintEx.Vec.cAnn)) :=
  cl_of_DRX drx_ann

end SanityX

end ApSpec.PipelineAnyTaintEx
