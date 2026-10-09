/-
  ApSpec.PipelineAnyTaint — the closures of the tail kind `[any-taint]` (decision F69) as instances
  of the communication pipeline (`ApSpec.Pipeline`, analyzer-core.md §5, §12).

  `AnyTaintDefs.lean` gives two new closures: run 1 with the rule W6T (`D6T`) and the restricted
  forward run with must-premises (`DRT`, over the objects `TObj`). This file encodes them as
  pipeline systems, as `PipelineAP.lean` does for `D` and `DR`. So the pipeline theorems
  (`Pipeline.reach_sound`, `quiescent_exact`, `no_lost_join`) apply to them: at quiescence the
  analyzer computes exactly `D6T` and `DRT`.

  ## 1. Run 1 with W6T: `sysD6T`

  `D6T` is `D` with `transferT` in place of `transfer` in `step` and `reqStmt`. So `sysD6T` is
  `sysD` with other local rules (`RuleD6T`); the objects (`PObj Obj`), the owners, the topics, the
  roots and the join (`JoinD`) are those of `sysD`:

  | closure rule                     | pipeline                                          | owner of the premises → conclusion |
  |----------------------------------|---------------------------------------------------|------------------------------------|
  | step, reqStmt (with `transferT`) | local rule `[edge M i n f]` (`RuleD6T.step`, `RuleD6T.reqStmt`) | M → M                |
  | every other rule of `D`          | the rule of `sysD` (`RuleD6T.keep`: `RuleD` on `noStmt P`) | as in `sysD`              |
  | ret                              | the join of `sysD` (`JoinD`)                      | M, topic callee                    |

  `noStmt P` is the program `P` without its statement edges (the same entry and exit nodes). On
  `noStmt P` the shared rules `CRule.step` and `CRule.reqStmt` (with `transfer`) never fire, and
  every other rule of `RuleD` reads the same edges as on `P` (call, cleaner and filter edges). So
  `RuleD6T.keep` is exactly the part of `sysD` that W6T does not change.

  ## 2. The restricted forward run with must-premises: `sysDRT`

  The objects are `TPObj`, over the objects `TObj` of `DRT`. The must flag of a premise (`mj`: the
  premise is `[any-taint]`, a must-premise) and the flag `am` of an added fact (`[any-taint]`:
  `.any` and normal on its link) are data of the objects:
    * `base o`               an object of `DRT`; owner: its method;
    * `link m a am M ic`     the callee `m` holds the link: the added fact `a` with its flag `am`,
                             from a caller edge of `M` with the premise `ic`; owner `m`;
    * `sub M i mi n' c a`    the caller's subscription: a caller edge with the premise `(i, mi)`
                             at the call `c` (return node `n'`) binds the fact `a`; owner `M`,
                             topic `c.callee`;
    * `pub m j mj g`         a published summary edge `(j, mj) → g` of `m`, after the restriction
                             by a demand edge of `m`; owner `m`, topic `m`.

  Rule by rule:

  | closure rule (`DRT`)             | pipeline                                          | owner of the premises → conclusion |
  |----------------------------------|---------------------------------------------------|------------------------------------|
  | root                             | root `base (init M zero false)`                   | – → M                              |
  | start (`startT`), step, reqStmt  | local rule on `base` objects                      | M → M                              |
  |   (`transferT`), pass, clean,    |                                                   |                                    |
  |   reqClean, filt, reqSink, vuln  |                                                   |                                    |
  | answer                           | local rule `[req M i t, added M a am]` → `init M (answerInit i a t) false` | M → M     |
  | initR (`emitTWith`)              | local rule `[added m a am]` → `init m j mj`       | m → m                              |
  | retRec (`recLayer`)              | local rule `[edge M i mi n f]` (records are fixed)| M → M                              |
  | added                            | `[edge M ic mc n f]` → `link c.callee a.fact am M ic`, with `am = a.fact.kind.isAny && !a.demand` | M → callee (MESSAGE) |
  |                                  | `[link m a am M ic]` → `added m a am`             | m → m                              |
  | reqUp                            | local rule AT THE CALLEE `[req m j t, link m a am M ic]` → `req M ic t` | m → M (MESSAGE) |
  | ret                              | `[edge M i mi n f]` → `sub M i mi n' c a`         | M → M                              |
  |                                  | `[init m j mj, edge m j mj (exit m) g]`, with `demand m d`, `restrict j g d = some g'` → `pub m j mj g'` | m → m |
  |                                  | JOIN `[sub M i mi n' c a]` `(pub c.callee j mj g)`, with `sat j a.fact` → `edge M i mi n' (limitF r')` | M, topic callee |

  What each object carries. A link carries the added fact with its flag `am` (`initR` and the
  emission read it, `answer` does not) and the caller premise `ic` (`reqUp` reads it). It does not
  carry the must flag `mc` of the caller premise: no rule reads it (the request `req M ic t` has no
  must flag). A subscription carries the must flag `mi` of the caller premise: the result of the
  join is an edge of the premise `(i, mi)`. A publication carries the must flag `mj` of the callee
  premise: in the spec the premise `[any-taint]` and the premise `[any]` are different premise keys
  (DESIGN §5). The join does not read `mj` (`DRT.ret` only carries it), and the layer of the
  result is as in `DR`. The rule for a record is local at the caller: the records are a fixed
  predicate, and the demotion `recLayer` of a must record applied by `applicable` only reads the
  record and the bound fact. `DRT` is a forward run, so `sysDRT` has no zero subscription and no
  zero publication.

  ## Main theorems (all parameters of the closures are variables)

    * `sysD6T_wf`, `sysDRT_wf`: the systems are well formed (`Sys.WF`).
    * `clD6T_iff`: `Cl sysD6T (.base o) ↔ D6T o`; `clDRT_iff`: `Cl sysDRT (.base o) ↔ DRT o`.
    * The other objects: `clD6T_link`, `clD6T_sub`, `clD6T_pub`, `clD6T_zsub`, `clD6T_zpub`;
      `clDRT_link`, `clDRT_sub`, `clDRT_pub`: a link, a subscription and a publication are exactly
      the data that the closure rules read.
    * The pipeline theorems for these systems: `known_D6T`, `known_DRT` (`Pipeline.reach_sound`:
      every processed object of a reachable state is in the closure); `result_D6T`, `result_DRT`
      (`Pipeline.quiescent_exact`: at a reachable quiescent state the processed `base` objects
      are exactly `D6T` / `DRT`); `no_lost_summary_D6T`, `no_lost_summary_DRT`
      (`Pipeline.no_lost_join`: the summary edge is never lost).
    * §5: the `Sanity` derivations of `AnyTaintDefs` (a normal `[any-taint]` source result) are in
      the pipeline closures, so the encodings are not vacuous.

  All proofs are constructive (`propext`, `Quot.sound` only; see the `#print axioms` lines).
-/
import ApSpec.PipelineProofs
import ApSpec.PipelineAP
import ApSpec.PipelineDriver
import ApSpec.AnyTaintDefs

namespace ApSpec.PipelineAnyTaint
open ApSpec ApSpec.Pipeline ApSpec.PipelineAP ApSpec.AnyTaint

/-! ## 1. The program without its statement edges -/

/-- `true` for a statement instruction. -/
def isStmtB : Instr → Bool
  | .stmt _ => true
  | _ => false

/-- The program `P` without its statement edges: the same entry and exit nodes, the call, cleaner
    and filter edges of `P`. On it the shared rules `CRule.step` and `CRule.reqStmt` of
    `PipelineAP` never fire. -/
def noStmt (P : Program) : Program :=
  ⟨P.entry, P.exit, P.edges.filter (fun e => !isStmtB e.2.2.1)⟩

theorem mem_of_noStmt {P : Program} {e : MethodId × Node × Instr × Node}
    (h : e ∈ (noStmt P).edges) : e ∈ P.edges :=
  (List.mem_filter.1 h).1

theorem noStmt_of_mem {P : Program} {M : MethodId} {n : Node} {ins : Instr} {n' : Node}
    (h : (M, n, ins, n') ∈ P.edges) (hs : isStmtB ins = false) :
    (M, n, ins, n') ∈ (noStmt P).edges := by
  refine List.mem_filter.2 ⟨h, ?_⟩
  show (!isStmtB ins) = true
  rw [hs]
  rfl

theorem stmt_not_noStmt {P : Program} {M : MethodId} {n : Node} {s : Stmt} {n' : Node} :
    (M, n, Instr.stmt s, n') ∉ (noStmt P).edges :=
  fun h => Bool.false_ne_true (List.mem_filter.1 h).2

theorem linkOK_noStmt {K : Type} {P : Program} {E : MethodId → K → Node → AFact → Prop}
    {m : MethodId} {a : PFact} {M : MethodId} {ic : K} :
    LinkOK (noStmt P) E m a M ic ↔ LinkOK P E m a M ic := by
  constructor
  · rintro ⟨n, f, n', c, e, a', hf, he, hc, he1, ha, hfa⟩
    exact ⟨n, f, n', c, e, a', hf, mem_of_noStmt he, hc, he1, ha, hfa⟩
  · rintro ⟨n, f, n', c, e, a', hf, he, hc, he1, ha, hfa⟩
    exact ⟨n, f, n', c, e, a', hf, noStmt_of_mem he rfl, hc, he1, ha, hfa⟩

theorem subOK_noStmt {K : Type} {P : Program} {E : MethodId → K → Node → AFact → Prop}
    {M : MethodId} {i : K} {n' : Node} {c : Call} {a : AFact} :
    SubOK (noStmt P) E M i n' c a ↔ SubOK P E M i n' c a := by
  constructor
  · rintro ⟨n, f, e, hf, he, he1, ha⟩
    exact ⟨n, f, e, hf, mem_of_noStmt he, he1, ha⟩
  · rintro ⟨n, f, e, hf, he, he1, ha⟩
    exact ⟨n, f, e, hf, noStmt_of_mem he rfl, he1, ha⟩

/-- The invariant of `PipelineAP` does not read the statement edges. -/
theorem inv_noStmt {P : Program} {R : Obj → Prop} {Pub : MethodId → PFact → AFact → Prop}
    {ZSub : MethodId → Node → Call → Prop} {ZPub : MethodId → AFact → Prop} {x : PO} :
    Inv (noStmt P) R Pub ZSub ZPub x ↔ Inv P R Pub ZSub ZPub x := by
  cases x with
  | base o => exact Iff.rfl
  | link m a M ic =>
    show LinkOK (noStmt P) (fun M i n f => R (.edge M i n f)) m a M ic ↔
      LinkOK P (fun M i n f => R (.edge M i n f)) m a M ic
    exact linkOK_noStmt
  | sub M i n' c a =>
    show SubOK (noStmt P) (fun M i n f => R (.edge M i n f)) M i n' c a ↔
      SubOK P (fun M i n f => R (.edge M i n f)) M i n' c a
    exact subOK_noStmt
  | pub m j g => exact Iff.rfl
  | zsub M n' c => exact Iff.rfl
  | zpub m g => exact Iff.rfl

#print axioms inv_noStmt

/-! ## 2. Run 1 with W6T: the closure `D6T` -/

section SysD6T
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- The local rules of `D6T`: the rules of `sysD` without the statement transfer (`keep`: `RuleD`
    on `noStmt P`), and the statement transfer with W6T (`step`, `reqStmt`: `transferT`). -/
inductive RuleD6T : List PO → PO → Prop where
  | keep {ps c} : RuleD (noStmt P) counted L α sinks ps c → RuleD6T ps c
  | step {M i n f n' s f'} : (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transferT taint counted L s f).facts →
      RuleD6T [.base (.edge M i n f)] (.base (.edge M i n' f'))
  | reqStmt {M i n f n' s t} : (M, n, Instr.stmt s, n') ∈ P.edges →
      t ∈ (transferT taint counted L s f).reqs →
      RuleD6T [.base (.edge M i n f)] (.base (.req M i t))

/-- Run 1 with W6T as a pipeline system: `sysD` with the local rules `RuleD6T`. The objects, the
    owners, the topics, the roots and the join are those of `sysD`. -/
def sysD6T : Sys PO MethodId MethodId :=
  { sysD P counted L α sinks roots with rule := RuleD6T P taint counted L α sinks }

/-- What a publication of `D6T` means. -/
def PubD6T (m : MethodId) (j : PFact) (g : AFact) : Prop :=
  D6T P taint counted L α sinks roots (.init m j) ∧
    D6T P taint counted L α sinks roots (.edge m j (P.exit m) g)

/-- The invariant of `sysD6T`. -/
abbrev InvD6T : PO → Prop :=
  Inv P (D6T P taint counted L α sinks roots) (PubD6T P taint counted L α sinks roots)
    (fun _ _ _ => False) (fun _ _ => False)

variable {P taint counted L α sinks roots}

/-- `D6T` is closed under the shared rules on `noStmt P` (the statement rules are vacuous). -/
theorem closedD6T : Closed (noStmt P) counted L sinks (D6T P taint counted L α sinks roots) where
  start := D6T.start
  step := fun _ he _ => absurd he stmt_not_noStmt
  reqStmt := fun _ he _ => absurd he stmt_not_noStmt
  pass := fun h he hm => D6T.pass h (mem_of_noStmt he) hm
  added := fun h he he1 ha => D6T.added h (mem_of_noStmt he) he1 ha
  reqSink := D6T.reqSink
  answer := D6T.answer
  reqUp := fun hr hf he hc he1 ha hcl hov => D6T.reqUp hr hf (mem_of_noStmt he) hc he1 ha hcl hov
  vuln := D6T.vuln
  clean := fun h he hf => D6T.clean h (mem_of_noStmt he) hf
  reqClean := fun h he ht => D6T.reqClean h (mem_of_noStmt he) ht
  filt := fun h he hp => D6T.filt h (mem_of_noStmt he) hp

#print axioms closedD6T

/-- `sysD6T` is well formed (`Pipeline.Sys.WF`). The rules of `keep` and the join are those of
    `sysD` (`PipelineAP.sysD_wf`); the two statement rules have one premise. -/
theorem sysD6T_wf : (sysD6T P taint counted L α sinks roots).WF where
  rule_ne := by
    intro ps c h
    cases h with
    | keep h =>
      exact (sysD_wf (P := noStmt P) (counted := counted) (L := L) (α := α) (sinks := sinks)
        (roots := roots)).rule_ne ps c h
    | step => exact List.cons_ne_nil _ _
    | reqStmt => exact List.cons_ne_nil _ _
  rule_local := by
    intro ps c h
    cases h with
    | keep h =>
      exact (sysD_wf (P := noStmt P) (counted := counted) (L := L) (α := α) (sinks := sinks)
        (roots := roots)).rule_local ps c h
    | step => exact local_one _
    | reqStmt => exact local_one _
  join_ne := (sysD_wf (P := P) (counted := counted) (L := L) (α := α) (sinks := sinks)
    (roots := roots)).join_ne
  join_sub := (sysD_wf (P := P) (counted := counted) (L := L) (α := α) (sinks := sinks)
    (roots := roots)).join_sub
  join_pub := (sysD_wf (P := P) (counted := counted) (L := L) (α := α) (sinks := sinks)
    (roots := roots)).join_pub
  join_owner := (sysD_wf (P := P) (counted := counted) (L := L) (α := α) (sinks := sinks)
    (roots := roots)).join_owner

#print axioms sysD6T_wf

/-- Soundness: every object of the pipeline closure satisfies its invariant. -/
theorem inv_of_clD6T {x : PO} (h : Cl (sysD6T P taint counted L α sinks roots) x) :
    InvD6T P taint counted L α sinks roots x := by
  induction h with
  | root hx =>
    obtain ⟨M, hM, rfl⟩ := mem_rootsOf hx
    exact D6T.root hM
  | rule hr _ ih =>
    cases hr with
    | keep hr =>
      cases hr with
      | common h =>
        exact inv_noStmt.1 (crule_sound closedD6T h (fun p hp => inv_noStmt.2 (ih p hp)))
      | initA => exact D6T.initA (fst_of ih :)
      | pub => exact ⟨(fst_of ih :), (snd_of ih :)⟩
    | step he hf => exact D6T.step (fst_of ih :) he hf
    | reqStmt he ht => exact D6T.reqStmt (fst_of ih :) he ht
  | join hj _ _ ihs ihp =>
    cases hj with
    | ret hap hr he2 hr' =>
      obtain ⟨_, _, _, hf, he, he1, ha⟩ := fst_of ihs
      exact D6T.ret hf he he1 ha ihp.1 hap ihp.2 hr he2 hr'

#print axioms inv_of_clD6T

/-- Completeness: every object of `D6T` is in the pipeline closure. -/
theorem cl_of_D6T {o : Obj} (h : D6T P taint counted L α sinks roots o) :
    Cl (sysD6T P taint counted L α sinks roots) (.base o) := by
  induction h with
  | root hM => exact Cl.root (root_mem_rootsOf hM)
  | start _ ih => exact Cl.rule (RuleD6T.keep (RuleD.common CRule.start)) (all_one ih)
  | step _ he hf ih => exact Cl.rule (RuleD6T.step he hf) (all_one ih)
  | reqStmt _ he ht ih => exact Cl.rule (RuleD6T.reqStmt he ht) (all_one ih)
  | pass _ he hm ih =>
    exact Cl.rule (RuleD6T.keep (RuleD.common (CRule.pass (noStmt_of_mem he rfl) hm)))
      (all_one ih)
  | added _ he he1 ha ih =>
    exact Cl.rule (RuleD6T.keep (RuleD.common CRule.added))
      (all_one (Cl.rule (RuleD6T.keep (RuleD.common (CRule.link (noStmt_of_mem he rfl) he1 ha)))
        (all_one ih)))
  | initA _ ih => exact Cl.rule (RuleD6T.keep RuleD.initA) (all_one ih)
  | ret _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    exact Cl.join (JoinD.ret hap hr he2 hr')
      (all_one (Cl.rule (RuleD6T.keep (RuleD.common (CRule.sub (noStmt_of_mem he rfl) he1 ha)))
        (all_one ihf)))
      (Cl.rule (RuleD6T.keep RuleD.pub) (all_two ihj ihg))
  | reqSink _ hs hc ih =>
    exact Cl.rule (RuleD6T.keep (RuleD.common (CRule.reqSink hs hc))) (all_one ih)
  | answer _ _ hm hov ihr iha =>
    exact Cl.rule (RuleD6T.keep (RuleD.common (CRule.answer hm hov))) (all_two ihr iha)
  | reqUp _ _ he hc he1 ha hcl hov ihr ihf =>
    subst hc
    exact Cl.rule (RuleD6T.keep (RuleD.common (CRule.reqUp hcl hov)))
      (all_two ihr (Cl.rule (RuleD6T.keep (RuleD.common (CRule.link (noStmt_of_mem he rfl) he1 ha)))
        (all_one ihf)))
  | vuln _ hs hc ih => exact Cl.rule (RuleD6T.keep (RuleD.common (CRule.vuln hs hc))) (all_one ih)
  | clean _ he hf ih =>
    exact Cl.rule (RuleD6T.keep (RuleD.common (CRule.clean (noStmt_of_mem he rfl) hf)))
      (all_one ih)
  | reqClean _ he ht ih =>
    exact Cl.rule (RuleD6T.keep (RuleD.common (CRule.reqClean (noStmt_of_mem he rfl) ht)))
      (all_one ih)
  | filt _ he hp ih =>
    exact Cl.rule (RuleD6T.keep (RuleD.common (CRule.filt (noStmt_of_mem he rfl) hp)))
      (all_one ih)

#print axioms cl_of_D6T

/-- THE THEOREM for run 1 with W6T: the pipeline closure on the closure objects is exactly
    `D6T`. -/
theorem clD6T_iff {o : Obj} :
    Cl (sysD6T P taint counted L α sinks roots) (.base o) ↔ D6T P taint counted L α sinks roots o :=
  ⟨fun h => inv_of_clD6T h, cl_of_D6T⟩

#print axioms clD6T_iff

/-- A link of `sysD6T` is exactly a binding of a caller edge of `D6T`. -/
theorem clD6T_link {m : MethodId} {a : PFact} {M : MethodId} {ic : PFact} :
    Cl (sysD6T P taint counted L α sinks roots) (.link m a M ic) ↔
      LinkOK P (fun M i n f => D6T P taint counted L α sinks roots (.edge M i n f)) m a M ic := by
  refine ⟨fun h => inv_of_clD6T h, ?_⟩
  rintro ⟨_, _, _, _, _, _, hf, he, rfl, he1, ha, rfl⟩
  exact Cl.rule (RuleD6T.keep (RuleD.common (CRule.link (noStmt_of_mem he rfl) he1 ha)))
    (all_one (cl_of_D6T hf))

#print axioms clD6T_link

/-- A subscription of `sysD6T` is exactly a binding of a caller edge of `D6T` at a call. -/
theorem clD6T_sub {M : MethodId} {i : PFact} {n' : Node} {c : Call} {a : AFact} :
    Cl (sysD6T P taint counted L α sinks roots) (.sub M i n' c a) ↔
      SubOK P (fun M i n f => D6T P taint counted L α sinks roots (.edge M i n f)) M i n' c a := by
  refine ⟨fun h => inv_of_clD6T h, ?_⟩
  rintro ⟨_, _, _, hf, he, he1, ha⟩
  exact Cl.rule (RuleD6T.keep (RuleD.common (CRule.sub (noStmt_of_mem he rfl) he1 ha)))
    (all_one (cl_of_D6T hf))

#print axioms clD6T_sub

/-- A publication of `sysD6T` is exactly an initial fact of `D6T` with an exit edge of it. -/
theorem clD6T_pub {m : MethodId} {j : PFact} {g : AFact} :
    Cl (sysD6T P taint counted L α sinks roots) (.pub m j g) ↔
      D6T P taint counted L α sinks roots (.init m j) ∧
        D6T P taint counted L α sinks roots (.edge m j (P.exit m) g) := by
  refine ⟨fun h => inv_of_clD6T h, ?_⟩
  rintro ⟨hj, hg⟩
  exact Cl.rule (RuleD6T.keep RuleD.pub) (all_two (cl_of_D6T hj) (cl_of_D6T hg))

#print axioms clD6T_pub

theorem clD6T_zsub {M : MethodId} {n' : Node} {c : Call} :
    ¬ Cl (sysD6T P taint counted L α sinks roots) (.zsub M n' c) := fun h => inv_of_clD6T h

#print axioms clD6T_zsub

theorem clD6T_zpub {m : MethodId} {g : AFact} :
    ¬ Cl (sysD6T P taint counted L α sinks roots) (.zpub m g) := fun h => inv_of_clD6T h

#print axioms clD6T_zpub

end SysD6T

/-! ## 3. The restricted forward run with must-premises: the closure `DRT` -/

deriving instance DecidableEq for TObj

/-- The pipeline objects of `DRT` (the objects `TObj` carry the must flags). -/
inductive TPObj where
  /-- an object of `DRT`; owner: its method -/
  | base (o : TObj)
  /-- the callee `m` holds the link: the added fact `a` with its flag `am` (`[any-taint]`), from a
      caller edge of `M` with the premise `ic` -/
  | link (m : MethodId) (a : PFact) (am : Bool) (M : MethodId) (ic : PFact)
  /-- the caller's subscription: caller premise `(i, mi)`, return node `n'`, call `c`, bound
      fact `a` -/
  | sub  (M : MethodId) (i : PFact) (mi : Bool) (n' : Node) (c : Call) (a : AFact)
  /-- a published summary edge `(j, mj) → g` of `m` -/
  | pub  (m : MethodId) (j : PFact) (mj : Bool) (g : AFact)
deriving DecidableEq

/-- The method of an object of `DRT`. -/
def tobjOwner : TObj → MethodId
  | .init M _ _ => M
  | .edge M _ _ _ _ => M
  | .added M _ _ => M
  | .req M _ _ => M
  | .vuln M _ _ _ => M

/-- The owner of a pipeline object of `DRT`. -/
def TPObj.owner : TPObj → MethodId
  | .base o => tobjOwner o
  | .link m _ _ _ _ => m
  | .sub M _ _ _ _ _ => M
  | .pub m _ _ _ => m

def TPObj.isSub : TPObj → Bool
  | .sub .. => true
  | _ => false

def TPObj.isPub : TPObj → Bool
  | .pub .. => true
  | _ => false

/-- The topic: the callee of a subscription, the publisher of a publication (and the owner for
    the other objects, which never meet a topic). -/
def TPObj.topic : TPObj → MethodId
  | .base o => tobjOwner o
  | .link m _ _ _ _ => m
  | .sub _ _ _ _ c _ => c.callee
  | .pub m _ _ _ => m

/-- The roots of a run with must flags: the zero fact of each root method, not a must-premise. -/
def rootsT (roots : List MethodId) : List TPObj :=
  roots.map (fun M => .base (.init M zeroFact false))

theorem mem_rootsT {roots : List MethodId} {x : TPObj} (h : x ∈ rootsT roots) :
    ∃ M, M ∈ roots ∧ x = .base (.init M zeroFact false) := by
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1 h
  exact ⟨M, hM, rfl⟩

theorem root_mem_rootsT {roots : List MethodId} {M : MethodId} (h : M ∈ roots) :
    (.base (.init M zeroFact false) : TPObj) ∈ rootsT roots :=
  List.mem_map.2 ⟨M, h, rfl⟩

section SysDRT
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → PFact × Bool × AFact → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- The local rules of `DRT`. -/
inductive RuleRT : List TPObj → TPObj → Prop where
  | start {M j mj} :
      RuleRT [.base (.init M j mj)] (.base (.edge M j mj (P.entry M) (startT j mj)))
  | step {M i mi n f n' s f'} : (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transferT taint counted L s f).facts →
      RuleRT [.base (.edge M i mi n f)] (.base (.edge M i mi n' f'))
  | reqStmt {M i mi n f n' s t} : (M, n, Instr.stmt s, n') ∈ P.edges →
      t ∈ (transferT taint counted L s f).reqs →
      RuleRT [.base (.edge M i mi n f)] (.base (.req M i t))
  | pass {M i mi n f n' c} : (M, n, Instr.call c, n') ∈ P.edges →
      memB f.fact.base c.touched = false →
      RuleRT [.base (.edge M i mi n f)] (.base (.edge M i mi n' f))
  /-- the caller sends the link to the callee (a message): the added fact with its flag -/
  | link {M i mi n f n' c e a} : (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts →
      RuleRT [.base (.edge M i mi n f)]
        (.link c.callee a.fact (a.fact.kind.isAny && !a.demand) M i)
  /-- the callee stores the added fact of a link, with its flag -/
  | added {m a am M ic} : RuleRT [.link m a am M ic] (.base (.added m a am))
  /-- the emission with the must flag (decision 8) -/
  | initR {m a am d j mj} : demand m d → emitTWith emit d.din a am = some (j, mj) →
      RuleRT [.base (.added m a am)] (.base (.init m j mj))
  /-- the caller subscribes at the call -/
  | sub {M i mi n f n' c e a} : (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts →
      RuleRT [.base (.edge M i mi n f)] (.sub M i mi n' c a)
  /-- the callee restricts a summary edge by one of its demand edges and publishes the result,
      with the must flag of its premise -/
  | pub {m j mj g d g'} : demand m d → restrict j g d = some g' →
      RuleRT [.base (.init m j mj), .base (.edge m j mj (P.exit m) g)] (.pub m j mj g')
  /-- a persisted record: a fixed predicate, so the rule is local at the caller; a must record
      applied by `applicable` only gives a demand result (`recLayer`) -/
  | retRec {M i mi n f n' c e1 a j mj g r e2 r'} : (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      recs c.callee (j, mj, g) → (sat j a.fact = true ∨ applicable j a.fact = true) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      RuleRT [.base (.edge M i mi n f)]
        (.base (.edge M i mi n' (limitF counted L (recLayer mj (sat j a.fact) r'))))
  | reqSink {M i mi n f s t} : (M, n, s) ∈ sinks → check i f s = .request t →
      RuleRT [.base (.edge M i mi n f)] (.base (.req M i t))
  | answer {M i t a am} : a.mark = .conc t → overlapB a i = true →
      RuleRT [.base (.req M i t), .base (.added M a am)]
        (.base (.init M (answerInit i a t) false))
  /-- the callee climbs a request through a link (the conclusion is a message to the caller) -/
  | reqUp {m j t a am M ic} : climbsB a.mark t = true → overlapB a j = true →
      RuleRT [.base (.req m j t), .link m a am M ic] (.base (.req M ic t))
  | vuln {M i mi n f s} : (M, n, s) ∈ sinks → check i f s = .triggered →
      RuleRT [.base (.edge M i mi n f)] (.base (.vuln M n s f.demand))
  | clean {M i mi n f n' cl f'} : (M, n, Instr.clean cl, n') ∈ P.edges →
      f' ∈ (cleanRes cl f).facts →
      RuleRT [.base (.edge M i mi n f)] (.base (.edge M i mi n' f'))
  | reqClean {M i mi n f n' cl t} : (M, n, Instr.clean cl, n') ∈ P.edges →
      t ∈ (cleanRes cl f).reqs →
      RuleRT [.base (.edge M i mi n f)] (.base (.req M i t))
  | filt {M i mi n f n' b may} : (M, n, Instr.filt b may, n') ∈ P.edges →
      (f.fact.base = b → may f.fact.path = true) →
      RuleRT [.base (.edge M i mi n f)] (.base (.edge M i mi n' f))

/-- The join of `DRT` (the rule `ret`): the subscription of the caller premise `(i, mi)` and a
    publication of the callee premise `(j, mj)`. The join reads `sat j a`, not `mj`. -/
inductive JoinRT : List TPObj → TPObj → TPObj → Prop where
  | ret {M i mi n' c a j mj g r e2 r'} : sat j a.fact = true →
      r ∈ (applySummary a j g).facts → e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      JoinRT [.sub M i mi n' c a] (.pub c.callee j mj g)
        (.base (.edge M i mi n' (limitF counted L r')))

/-- The restricted forward run with must-premises as a pipeline system. -/
def sysDRT : Sys TPObj MethodId MethodId where
  owner := TPObj.owner
  roots := rootsT roots
  rule  := RuleRT P taint counted L demand emit sat restrict recs sinks
  isSub := TPObj.isSub
  isPub := TPObj.isPub
  topic := TPObj.topic
  join  := JoinRT counted L sat

/-- What a link means: a caller edge of `M` with the premise `ic` (any must flag), at a call of
    `m`, binds a fact `a'` whose path fact is `a` and whose flag is `am`. -/
def LinkOKT (E : MethodId → PFact → Bool → Node → AFact → Prop) (m : MethodId) (a : PFact)
    (am : Bool) (M : MethodId) (ic : PFact) : Prop :=
  ∃ (mc : Bool) (n : Node) (f : AFact) (n' : Node) (c : Call) (e : MicroEdge) (a' : AFact),
    E M ic mc n f ∧ (M, n, Instr.call c, n') ∈ P.edges ∧ c.callee = m ∧
    e ∈ c.toCallee ∧ a' ∈ (applyEdge f e.1 e.2).facts ∧ a'.fact = a ∧
    (a'.fact.kind.isAny && !a'.demand) = am

/-- What a subscription means: a caller edge of `M` with the premise `(i, mi)`, at the call `c`
    with the return node `n'`, binds the fact `a`. -/
def SubOKT (E : MethodId → PFact → Bool → Node → AFact → Prop) (M : MethodId) (i : PFact)
    (mi : Bool) (n' : Node) (c : Call) (a : AFact) : Prop :=
  ∃ (n : Node) (f : AFact) (e : MicroEdge),
    E M i mi n f ∧ (M, n, Instr.call c, n') ∈ P.edges ∧ e ∈ c.toCallee ∧
    a ∈ (applyEdge f e.1 e.2).facts

/-- What a publication means: a summary edge of the premise `(j, mj)` of `m`, restricted by a
    demand edge of `m`. -/
def PubRT (R : TObj → Prop) (m : MethodId) (j : PFact) (mj : Bool) (g' : AFact) : Prop :=
  ∃ (g : AFact) (d : DemandEdge), R (.init m j mj) ∧ R (.edge m j mj (P.exit m) g) ∧
    demand m d ∧ restrict j g d = some g'

/-- The invariant of a pipeline object of `DRT`: what it means in terms of the closure `R`. -/
def InvT (R : TObj → Prop) : TPObj → Prop
  | .base o => R o
  | .link m a am M ic => LinkOKT P (fun M i mi n f => R (.edge M i mi n f)) m a am M ic
  | .sub M i mi n' c a => SubOKT P (fun M i mi n f => R (.edge M i mi n f)) M i mi n' c a
  | .pub m j mj g => PubRT P demand restrict R m j mj g

/-- The invariant of `sysDRT`. -/
abbrev InvDRT : TPObj → Prop :=
  InvT P demand restrict (DRT P taint counted L demand emit sat restrict recs sinks roots)

/-- A set of objects closed under the rules of `DRT` (other than the root). -/
structure ClosedRT (R : TObj → Prop) : Prop where
  start : ∀ {M j mj}, R (.init M j mj) → R (.edge M j mj (P.entry M) (startT j mj))
  step : ∀ {M i mi n f n' s f'}, R (.edge M i mi n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
    f' ∈ (transferT taint counted L s f).facts → R (.edge M i mi n' f')
  reqStmt : ∀ {M i mi n f n' s t}, R (.edge M i mi n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
    t ∈ (transferT taint counted L s f).reqs → R (.req M i t)
  pass : ∀ {M i mi n f n' c}, R (.edge M i mi n f) → (M, n, Instr.call c, n') ∈ P.edges →
    memB f.fact.base c.touched = false → R (.edge M i mi n' f)
  added : ∀ {M i mi n f n' c e a}, R (.edge M i mi n f) → (M, n, Instr.call c, n') ∈ P.edges →
    e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
    R (.added c.callee a.fact (a.fact.kind.isAny && !a.demand))
  initR : ∀ {m a am d j mj}, R (.added m a am) → demand m d →
    emitTWith emit d.din a am = some (j, mj) → R (.init m j mj)
  ret : ∀ {M i mi n f n' c e1 a j mj g d g' r e2 r'}, R (.edge M i mi n f) →
    (M, n, Instr.call c, n') ∈ P.edges → e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
    R (.init c.callee j mj) → R (.edge c.callee j mj (P.exit c.callee) g) →
    demand c.callee d → restrict j g d = some g' → sat j a.fact = true →
    r ∈ (applySummary a j g').facts → e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
    R (.edge M i mi n' (limitF counted L r'))
  retRec : ∀ {M i mi n f n' c e1 a j mj g r e2 r'}, R (.edge M i mi n f) →
    (M, n, Instr.call c, n') ∈ P.edges → e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
    recs c.callee (j, mj, g) → (sat j a.fact = true ∨ applicable j a.fact = true) →
    r ∈ (applySummary a j g).facts → e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
    R (.edge M i mi n' (limitF counted L (recLayer mj (sat j a.fact) r')))
  reqSink : ∀ {M i mi n f s t}, R (.edge M i mi n f) → (M, n, s) ∈ sinks →
    check i f s = .request t → R (.req M i t)
  answer : ∀ {M i t a am}, R (.req M i t) → R (.added M a am) → a.mark = .conc t →
    overlapB a i = true → R (.init M (answerInit i a t) false)
  reqUp : ∀ {m j t M ic mc n f n' c e a}, R (.req m j t) → R (.edge M ic mc n f) →
    (M, n, Instr.call c, n') ∈ P.edges → c.callee = m → e ∈ c.toCallee →
    a ∈ (applyEdge f e.1 e.2).facts → climbsB a.fact.mark t = true →
    overlapB a.fact j = true → R (.req M ic t)
  vuln : ∀ {M i mi n f s}, R (.edge M i mi n f) → (M, n, s) ∈ sinks →
    check i f s = .triggered → R (.vuln M n s f.demand)
  clean : ∀ {M i mi n f n' cl f'}, R (.edge M i mi n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
    f' ∈ (cleanRes cl f).facts → R (.edge M i mi n' f')
  reqClean : ∀ {M i mi n f n' cl t}, R (.edge M i mi n f) →
    (M, n, Instr.clean cl, n') ∈ P.edges → t ∈ (cleanRes cl f).reqs → R (.req M i t)
  filt : ∀ {M i mi n f n' b may}, R (.edge M i mi n f) → (M, n, Instr.filt b may, n') ∈ P.edges →
    (f.fact.base = b → may f.fact.path = true) → R (.edge M i mi n' f)

variable {P taint counted L demand emit sat restrict recs sinks roots}

/-- `DRT` is closed under its rules. -/
theorem closedDRT : ClosedRT P taint counted L demand emit sat restrict recs sinks
    (DRT P taint counted L demand emit sat restrict recs sinks roots) where
  start := DRT.start
  step := DRT.step
  reqStmt := DRT.reqStmt
  pass := DRT.pass
  added := DRT.added
  initR := DRT.initR
  ret := DRT.ret
  retRec := DRT.retRec
  reqSink := DRT.reqSink
  answer := DRT.answer
  reqUp := DRT.reqUp
  vuln := DRT.vuln
  clean := DRT.clean
  reqClean := DRT.reqClean
  filt := DRT.filt

#print axioms closedDRT

/-- The local rules preserve the invariant of every closed set. -/
theorem ruleRT_sound {R : TObj → Prop}
    (hR : ClosedRT P taint counted L demand emit sat restrict recs sinks R)
    {ps : List TPObj} {c : TPObj}
    (h : RuleRT P taint counted L demand emit sat restrict recs sinks ps c)
    (hps : ∀ p ∈ ps, InvT P demand restrict R p) : InvT P demand restrict R c := by
  cases h with
  | start => exact hR.start (fst_of hps :)
  | step he hf => exact hR.step (fst_of hps :) he hf
  | reqStmt he ht => exact hR.reqStmt (fst_of hps :) he ht
  | pass he hm => exact hR.pass (fst_of hps :) he hm
  | link he he1 ha => exact ⟨_, _, _, _, _, _, _, (fst_of hps :), he, rfl, he1, ha, rfl, rfl⟩
  | added =>
    obtain ⟨_, _, _, _, _, _, _, hf, he, rfl, he1, ha, rfl, rfl⟩ := fst_of hps
    exact hR.added hf he he1 ha
  | initR hd he => exact hR.initR (fst_of hps :) hd he
  | sub he he1 ha => exact ⟨_, _, _, (fst_of hps :), he, he1, ha⟩
  | pub hd hres => exact ⟨_, _, (fst_of hps :), (snd_of hps :), hd, hres⟩
  | retRec he he1 ha hrec hs hr he2 hr' =>
    exact hR.retRec (fst_of hps :) he he1 ha hrec hs hr he2 hr'
  | reqSink hs hc => exact hR.reqSink (fst_of hps :) hs hc
  | answer hm hov => exact hR.answer (fst_of hps :) (snd_of hps :) hm hov
  | reqUp hcl hov =>
    obtain ⟨_, _, _, _, _, _, _, hf, he, hc, he1, ha, rfl, _⟩ := snd_of hps
    exact hR.reqUp (fst_of hps :) hf he hc he1 ha hcl hov
  | vuln hs hc => exact hR.vuln (fst_of hps :) hs hc
  | clean he hf => exact hR.clean (fst_of hps :) he hf
  | reqClean he ht => exact hR.reqClean (fst_of hps :) he ht
  | filt he hp => exact hR.filt (fst_of hps :) he hp

#print axioms ruleRT_sound

/-- The join preserves the invariant of every closed set. -/
theorem joinRT_sound {R : TObj → Prop}
    (hR : ClosedRT P taint counted L demand emit sat restrict recs sinks R)
    {ss : List TPObj} {p c : TPObj} (h : JoinRT counted L sat ss p c)
    (hss : ∀ s ∈ ss, InvT P demand restrict R s) (hp : InvT P demand restrict R p) :
    InvT P demand restrict R c := by
  cases h with
  | ret hs hr he2 hr' =>
    obtain ⟨_, _, _, hf, he, he1, ha⟩ := (fst_of hss :)
    obtain ⟨_, _, hj, hg, hd, hres⟩ := hp
    exact hR.ret hf he he1 ha hj hg hd hres hs hr he2 hr'

#print axioms joinRT_sound

theorem ruleRT_ne {ps : List TPObj} {c : TPObj}
    (h : RuleRT P taint counted L demand emit sat restrict recs sinks ps c) : ps ≠ [] := by
  cases h <;> exact List.cons_ne_nil _ _

theorem ruleRT_local {ps : List TPObj} {c : TPObj}
    (h : RuleRT P taint counted L demand emit sat restrict recs sinks ps c) :
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

theorem joinRT_shape {ss : List TPObj} {p c : TPObj} (h : JoinRT counted L sat ss p c) :
    ss ≠ [] ∧ (∀ s ∈ ss, s.isSub = true ∧ s.topic = p.topic) ∧ p.isPub = true ∧
      (∀ s ∈ ss, ∀ s' ∈ ss, s.owner = s'.owner) := by
  cases h
  refine ⟨List.cons_ne_nil _ _, ?_, rfl, local_one _⟩
  intro s hs
  rw [mem_one hs]
  exact ⟨rfl, rfl⟩

/-- `sysDRT` is well formed (`Pipeline.Sys.WF`): every local rule has at least one premise, all of
    one owner (`answer`, `reqUp` and `pub` have two premises of one method); the join has one
    subscription, of the topic of its publication. -/
theorem sysDRT_wf :
    (sysDRT P taint counted L demand emit sat restrict recs sinks roots).WF where
  rule_ne := fun _ _ h => ruleRT_ne h
  rule_local := fun _ _ h => ruleRT_local h
  join_ne := fun _ _ _ h => (joinRT_shape h).1
  join_sub := fun _ _ _ h => (joinRT_shape h).2.1
  join_pub := fun _ _ _ h => (joinRT_shape h).2.2.1
  join_owner := fun _ _ _ h => (joinRT_shape h).2.2.2

#print axioms sysDRT_wf

/-- Soundness: every object of the pipeline closure satisfies its invariant. -/
theorem inv_of_clDRT {x : TPObj}
    (h : Cl (sysDRT P taint counted L demand emit sat restrict recs sinks roots) x) :
    InvDRT P taint counted L demand emit sat restrict recs sinks roots x := by
  induction h with
  | root hx =>
    obtain ⟨M, hM, rfl⟩ := mem_rootsT hx
    exact DRT.root hM
  | rule hr _ ih => exact ruleRT_sound closedDRT hr ih
  | join hj _ _ ihs ihp => exact joinRT_sound closedDRT hj ihs ihp

#print axioms inv_of_clDRT

/-- Completeness: every object of `DRT` is in the pipeline closure. -/
theorem cl_of_DRT {o : TObj} (h : DRT P taint counted L demand emit sat restrict recs sinks roots o) :
    Cl (sysDRT P taint counted L demand emit sat restrict recs sinks roots) (.base o) := by
  induction h with
  | root hM => exact Cl.root (root_mem_rootsT hM)
  | start _ ih => exact Cl.rule RuleRT.start (all_one ih)
  | step _ he hf ih => exact Cl.rule (RuleRT.step he hf) (all_one ih)
  | reqStmt _ he ht ih => exact Cl.rule (RuleRT.reqStmt he ht) (all_one ih)
  | pass _ he hm ih => exact Cl.rule (RuleRT.pass he hm) (all_one ih)
  | added _ he he1 ha ih =>
    exact Cl.rule RuleRT.added (all_one (Cl.rule (RuleRT.link he he1 ha) (all_one ih)))
  | initR _ hd he ih => exact Cl.rule (RuleRT.initR hd he) (all_one ih)
  | ret _ he he1 ha _ _ hd hres hs hr he2 hr' ihf ihj ihg =>
    exact Cl.join (JoinRT.ret hs hr he2 hr')
      (all_one (Cl.rule (RuleRT.sub he he1 ha) (all_one ihf)))
      (Cl.rule (RuleRT.pub hd hres) (all_two ihj ihg))
  | retRec _ he he1 ha hrec hs hr he2 hr' ih =>
    exact Cl.rule (RuleRT.retRec he he1 ha hrec hs hr he2 hr') (all_one ih)
  | reqSink _ hs hc ih => exact Cl.rule (RuleRT.reqSink hs hc) (all_one ih)
  | answer _ _ hm hov ihr iha => exact Cl.rule (RuleRT.answer hm hov) (all_two ihr iha)
  | reqUp _ _ he hc he1 ha hcl hov ihr ihf =>
    subst hc
    exact Cl.rule (RuleRT.reqUp hcl hov)
      (all_two ihr (Cl.rule (RuleRT.link he he1 ha) (all_one ihf)))
  | vuln _ hs hc ih => exact Cl.rule (RuleRT.vuln hs hc) (all_one ih)
  | clean _ he hf ih => exact Cl.rule (RuleRT.clean he hf) (all_one ih)
  | reqClean _ he ht ih => exact Cl.rule (RuleRT.reqClean he ht) (all_one ih)
  | filt _ he hp ih => exact Cl.rule (RuleRT.filt he hp) (all_one ih)

#print axioms cl_of_DRT

/-- THE THEOREM for the restricted forward run with must-premises: the pipeline closure on the
    closure objects is exactly `DRT` (with the must flags of the premises and the flags of the
    added facts). -/
theorem clDRT_iff {o : TObj} :
    Cl (sysDRT P taint counted L demand emit sat restrict recs sinks roots) (.base o) ↔
      DRT P taint counted L demand emit sat restrict recs sinks roots o :=
  ⟨fun h => inv_of_clDRT h, cl_of_DRT⟩

#print axioms clDRT_iff

/-- A link of `sysDRT` is exactly a binding of a caller edge of `DRT` (with any must flag of the
    caller premise), with the flag `am` of the bound fact. -/
theorem clDRT_link {m : MethodId} {a : PFact} {am : Bool} {M : MethodId} {ic : PFact} :
    Cl (sysDRT P taint counted L demand emit sat restrict recs sinks roots) (.link m a am M ic) ↔
      LinkOKT P (fun M i mi n f => DRT P taint counted L demand emit sat restrict recs sinks roots
        (.edge M i mi n f)) m a am M ic := by
  refine ⟨fun h => inv_of_clDRT h, ?_⟩
  rintro ⟨_, _, _, _, _, _, _, hf, he, rfl, he1, ha, rfl, rfl⟩
  exact Cl.rule (RuleRT.link he he1 ha) (all_one (cl_of_DRT hf))

#print axioms clDRT_link

/-- A subscription of `sysDRT` is exactly a binding of a caller edge of `DRT` at a call, with the
    must flag of the caller premise. -/
theorem clDRT_sub {M : MethodId} {i : PFact} {mi : Bool} {n' : Node} {c : Call} {a : AFact} :
    Cl (sysDRT P taint counted L demand emit sat restrict recs sinks roots) (.sub M i mi n' c a) ↔
      SubOKT P (fun M i mi n f => DRT P taint counted L demand emit sat restrict recs sinks roots
        (.edge M i mi n f)) M i mi n' c a := by
  refine ⟨fun h => inv_of_clDRT h, ?_⟩
  rintro ⟨_, _, _, hf, he, he1, ha⟩
  exact Cl.rule (RuleRT.sub he he1 ha) (all_one (cl_of_DRT hf))

#print axioms clDRT_sub

/-- A publication of `sysDRT` is exactly a summary edge of a premise `(j, mj)` of `DRT`, restricted
    by a demand edge of its method. -/
theorem clDRT_pub {m : MethodId} {j : PFact} {mj : Bool} {g' : AFact} :
    Cl (sysDRT P taint counted L demand emit sat restrict recs sinks roots) (.pub m j mj g') ↔
      ∃ (g : AFact) (d : DemandEdge),
        DRT P taint counted L demand emit sat restrict recs sinks roots (.init m j mj) ∧
        DRT P taint counted L demand emit sat restrict recs sinks roots
          (.edge m j mj (P.exit m) g) ∧
        demand m d ∧ restrict j g d = some g' := by
  refine ⟨fun h => inv_of_clDRT h, ?_⟩
  rintro ⟨_, _, hj, hg, hd, hres⟩
  exact Cl.rule (RuleRT.pub hd hres) (all_two (cl_of_DRT hj) (cl_of_DRT hg))

#print axioms clDRT_pub

end SysDRT

/-! ## 4. The pipeline theorems for `sysD6T` and `sysDRT`

  The theorems of `PipelineProofs.lean` are generic over the system (`Pipeline.Sys`), so they
  apply to the two encodings with `sysD6T_wf` and `sysDRT_wf`. -/

/-- What the driver reads from the final state of a run with must flags: the closure objects that
    it holds (as `PipelineDriver.result` for the objects `Obj`). -/
def resultT (st : St TPObj MethodId MethodId) : TObj → Prop := fun o => TPObj.base o ∈ st.known

section Instances
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}

section RunD6T
variable {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId} {st : St PO MethodId MethodId}

/-- Soundness of a run of `sysD6T` (`Pipeline.reach_sound`): at every reachable state (quiescent
    or not), every processed closure object is an object of `D6T`. -/
theorem known_D6T (hR : Pipeline.Reach (sysD6T P taint counted L α sinks roots) st) {o : Obj}
    (h : PObj.base o ∈ st.known) : D6T P taint counted L α sinks roots o :=
  inv_of_clD6T ((reach_sound hR).known _ h)

#print axioms known_D6T

/-- A complete run 1 with W6T (`Pipeline.quiescent_exact`): at a reachable quiescent state the
    driver reads exactly `D6T`. -/
theorem result_D6T (hR : Pipeline.Reach (sysD6T P taint counted L α sinks roots) st)
    (hQ : st.Quiescent) : PipelineDriver.result st = D6T P taint counted L α sinks roots := by
  funext o
  exact propext ((quiescent_exact sysD6T_wf hR hQ).trans clD6T_iff)

#print axioms result_D6T

/-- The summary edge is never lost in run 1 with W6T (`Pipeline.no_lost_join`): at a reachable
    quiescent state, a processed subscription and a processed publication that satisfy the
    condition of `D6T.ret` have their caller edge processed. -/
theorem no_lost_summary_D6T (hR : Pipeline.Reach (sysD6T P taint counted L α sinks roots) st)
    (hQ : st.Quiescent) {M : MethodId} {i : PFact} {n' : Node} {c : Call} {a : AFact}
    {j : PFact} {g r : AFact} {e2 : MicroEdge} {r' : AFact}
    (hs : PObj.sub M i n' c a ∈ st.known) (hp : PObj.pub c.callee j g ∈ st.known)
    (hap : applicable j a.fact = true) (hr : r ∈ (applySummary a j g).facts)
    (he2 : e2 ∈ c.fromCallee) (hr' : r' ∈ (applyEdge r e2.1 e2.2).facts) :
    PObj.base (.edge M i n' (limitF counted L r')) ∈ st.known :=
  no_lost_join sysD6T_wf hR hQ (JoinD.ret hap hr he2 hr') (all_one hs) hp

#print axioms no_lost_summary_D6T

end RunD6T

section RunDRT
variable {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × Bool × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId} {st : St TPObj MethodId MethodId}

/-- Soundness of a run of `sysDRT` (`Pipeline.reach_sound`): at every reachable state (quiescent
    or not), every processed closure object is an object of `DRT`, with its must flags. -/
theorem known_DRT
    (hR : Pipeline.Reach (sysDRT P taint counted L demand emit sat restrict recs sinks roots) st)
    {o : TObj} (h : TPObj.base o ∈ st.known) :
    DRT P taint counted L demand emit sat restrict recs sinks roots o :=
  inv_of_clDRT ((reach_sound hR).known _ h)

#print axioms known_DRT

/-- A COMPLETE RESTRICTED FORWARD RUN WITH MUST-PREMISES (`Pipeline.quiescent_exact`): at a
    reachable quiescent state the driver reads exactly `DRT` (the initial facts and the edges with
    their must flags, the added facts with their flags, the requests and the vulnerabilities). So
    every theorem on `DRT` holds for the result of the analyzer. -/
theorem result_DRT
    (hR : Pipeline.Reach (sysDRT P taint counted L demand emit sat restrict recs sinks roots) st)
    (hQ : st.Quiescent) :
    resultT st = DRT P taint counted L demand emit sat restrict recs sinks roots := by
  funext o
  exact propext ((quiescent_exact sysDRT_wf hR hQ).trans clDRT_iff)

#print axioms result_DRT

/-- The summary edge is never lost in a restricted forward run with must-premises
    (`Pipeline.no_lost_join`): at a reachable quiescent state, a processed subscription of the
    caller premise `(i, mi)` and a processed publication of the callee premise `(j, mj)` with
    `sat j a` have their caller edge of the premise `(i, mi)` processed. -/
theorem no_lost_summary_DRT
    (hR : Pipeline.Reach (sysDRT P taint counted L demand emit sat restrict recs sinks roots) st)
    (hQ : st.Quiescent) {M : MethodId} {i : PFact} {mi : Bool} {n' : Node} {c : Call}
    {a : AFact} {j : PFact} {mj : Bool} {g r : AFact} {e2 : MicroEdge} {r' : AFact}
    (hs : TPObj.sub M i mi n' c a ∈ st.known) (hp : TPObj.pub c.callee j mj g ∈ st.known)
    (hsat : sat j a.fact = true) (hr : r ∈ (applySummary a j g).facts)
    (he2 : e2 ∈ c.fromCallee) (hr' : r' ∈ (applyEdge r e2.1 e2.2).facts) :
    TPObj.base (.edge M i mi n' (limitF counted L r')) ∈ st.known :=
  no_lost_join sysDRT_wf hR hQ (JoinRT.ret hsat hr he2 hr') (all_one hs) hp

#print axioms no_lost_summary_DRT

end RunDRT
end Instances

/-! ## 5. Sanity: the derivations of `AnyTaintDefs.Sanity` in the pipeline closure

  The source result `[any-taint]` (a normal `.any` edge) of run 1 and of a restricted run is an
  object of the encoded systems (so the encodings are not vacuous on the new layer rule). -/

example : Cl (sysD6T Sanity.P Sanity.taintSrc Sanity.cnt 3 policy1 [] [0])
    (.base (.edge 0 zeroFact 1 Sanity.fNormal)) :=
  cl_of_D6T Sanity.d6t_src

example : Cl (sysDRT Sanity.P Sanity.taintSrc Sanity.cnt 3 (fun _ _ => False) emitM satI restrictU
    (fun _ _ => False) [] [0]) (.base (.edge 0 zeroFact false 1 Sanity.fNormal)) :=
  cl_of_DRT Sanity.drt_src

end ApSpec.PipelineAnyTaint
