/-
  ApSpec.PipelineAP — the AP closures as instances of the communication pipeline
  (`ApSpec.Pipeline`, analyzer-core.md §5, §6).

  The encoding: the ACTORS are the methods (`Actor := MethodId`), the TOPICS are the callees
  (`Topic := MethodId`). The pipeline objects (`PObj O`, for the objects `O` of a closure) are
    * `base o`              an object of the closure; owner: its method;
    * `link m a M ic`       the callee `m` holds the link: the added fact `a`, from a caller edge of
                            `M` with the premise `ic`; owner `m` (the callee);
    * `sub M i n' c a`      the caller's subscription: a caller edge with the premise `i` at the
                            call `c` (return node `n'`) binds the fact `a` into the callee;
                            owner `M`, topic `c.callee`;
    * `pub m j g`           a published summary edge `j → g` of `m` (in a restricted run: after
                            the restriction by a demand edge of `m`); owner `m`, topic `m`;
    * `zsub M n' c`         backward run: the zero fact of `M` at the call `c`; owner `M`,
                            topic `c.callee`;
    * `zpub m g`            backward run: a zero-premise summary `zero → g` of `m`; owner `m`,
                            topic `m`.

  Rule by rule (`CRule` holds the rules that all three closures share; the premises of a local
  rule have ONE owner, the conclusion of a local rule may have another owner: a message):

  | closure rule                     | pipeline                                          | owner of the premises → conclusion |
  |----------------------------------|---------------------------------------------------|------------------------------------|
  | root                             | root `base (init M zero)`                         | – → M                              |
  | start, step, reqStmt, pass,      | local rule on `base` objects                      | M → M                              |
  |   clean, reqClean, filt,         |                                                   |                                    |
  |   reqSink, vuln                  |                                                   |                                    |
  | answer                           | local rule `[req M i t, added M a]`               | M → M                              |
  | initA (D), initR (DR, DB)        | local rule `[added m a]`                          | m → m                              |
  | retRec (DR, DB)                  | local rule `[edge M i n f]` (records are fixed)   | M → M                              |
  | added                            | `[edge M ic n f]` → `link c.callee a M ic`        | M → callee (MESSAGE)               |
  |                                  | `[link m a M ic]` → `added m a`                   | m → m                              |
  | reqUp                            | local rule AT THE CALLEE `[req m j t, link m a M ic]` → `req M ic t` | m → M (MESSAGE) |
  | ret                              | `[edge M i n f]` → `sub M i n' c a`               | M → M                              |
  |                                  | `[init m j, edge m j (exit m) g]` → `pub m j g`   | m → m                              |
  |                                  |   (DR, DB: with `demand m d`, `restrict j g d = some g'`, → `pub m j g'`) |  |
  |                                  | JOIN `[sub M i n' c a]` `(pub c.callee j g)` → `edge M i n' (limitF r')` | M, topic callee |
  | zpass, seed (DB)                 | local rule `[edge M zero n zero]`                 | M → M                              |
  | zin (DB)                         | `[edge M zero n zero]` → `init c.callee zero`     | M → callee (MESSAGE)               |
  | zret (DB)                        | `[edge M zero n zero]` → `zsub M n' c`            | M → M                              |
  |                                  | `[edge m zero (exit m) g]` → `zpub m g`           | m → m                              |
  |                                  | JOIN `[zsub M n' c]` `(zpub c.callee g)` → `edge M zero n' (limitF r')` | M, topic callee |

  Why each premise has its owner: `reqUp` reads a request of the callee and a caller edge; the
  callee keeps the caller edge in the link (it already receives it with the added fact), so the
  rule is local at the callee and its conclusion (a request of the caller) is a message. `ret`
  reads a caller edge and two callee objects; the caller part becomes a subscription, the callee
  part a publication, and the side conditions are split: what the caller knows (the call, the
  binding, the bound fact `a`) is in the subscription rule, what the callee knows (the initial
  fact, the exit edge, the demand and the restriction) is in the publication rule, and what
  needs both (`applicable j a` / `sat j a`, the summary application and the binding back) is in
  the join. A link, a subscription and a publication carry exactly the data the rules read.

  The zero subscription `zsub` is made only when `zbind = true` (the user's design); with the
  plain reversal there is no `zsub`, so no `zret`, exactly as in `DB`. The zero publication is
  NOT restricted (spec §5.3 E4), the ordinary publication is.

  `Statics.DS` (§6) uses the same objects over `SObj`; the rules that differ from `D`:

  | closure rule                     | pipeline                                          | owner of the premises → conclusion |
  |----------------------------------|---------------------------------------------------|------------------------------------|
  | step, reqStmt (with `sKeepP`)    | local rule `[edge M i n f]`                       | M → M                              |
  | sreqStmt (raise)                 | local rule `[edge M i n f]` → `sreq M i (reqP p)` | M → M                              |
  | sanswer (answer)                 | local rule `[sreq M i p, added M a]`              | M → M                              |
  | sreqUp (climb)                   | local rule AT THE CALLEE `[sreq m j p, link m a M ic]` → `sreq M ic p` (`climbOK ic a p`) | m → M (MESSAGE) |
  | sret (overlap reading)           | a second JOIN of `sub` and `pub` (`fbOK i a j`)   | M, topic callee                    |

  `ND.DN` (§7) has its own objects `NPObj`: the link and the subscription carry the PREMISE LIST
  of the caller edge (`reqUp` reads a link with a singleton list), the subscription also names
  its call statement `sub M Pf n n' c a` (the partial matches of `DN` are per call statement),
  and a summary with several premises has its own publication `ndpub m Pc g`:

  | closure rule                     | pipeline                                          | owner of the premises → conclusion |
  |----------------------------------|---------------------------------------------------|------------------------------------|
  | ret (one premise)                | as in `D`: JOIN `[sub M P n n' c a]` `(pub c.callee j g)` | M, topic callee            |
  | ndOpen, ndBind, ndRet            | `[nedge m Pc (exit m) g]`, `2 ≤ |Pc|` → `ndpub m Pc g` | m → m                         |
  |   (several premises)             | k-ARY JOIN `ss` `(ndpub c.callee Pc g)` → `nedge M P n' (limitF r)`, with `Combo M n n' c Pc ss P d`: one subscription per premise, in order, all at the call statement `(M, n, c, n')` | M, topic callee |
  | conj                             | local rule `[nedge M P1 n f1, nedge M P2 n f2]`   | M → M                              |
  | reqConj, the lifted rules of `D` | as in `D`                                         |                                    |

  This is the design of spec §5.4 and of the k-ary `join` of `Pipeline.Sys`: the k-ary join
  gives what `DN.ndRet` gives after `DN.ndOpen` and one `DN.ndBind` per premise (`combo_chain`).
  The standing partial match `npart` of `DN` is the state of that join inside the caller (the
  conjunction store), not a pipeline object (`clDN_npart`). An alternative that keeps `npart` as
  an object (a unary join opening the match, `ndBind` and `ndRet` local at the caller) also
  works, but `DN.ndOpen` has no caller premise, so `DN` holds partial matches at call statements
  that no subscription reaches; the k-ary join has no such residue.

  With the pipeline theorem `quiescent_exact` (`PipelineProofs.lean`) and `*_wf`, the `base`
  objects that a reachable quiescent state knows are exactly the objects of the closure.

  Main theorems (all parameters of the closures are variables):
    * `sysD_wf`, `sysDR_wf`, `sysDB_wf`, `sysDS_wf`, `sysDN_wf`: the systems are well formed
      (`Sys.WF`).
    * `clD_iff`, `clDR_iff`, `clDB_iff`, `clDS_iff`: `Cl S (.base o) ↔ <closure> o`.
    * `clDN_iff`: `Cl S (.base o) ↔ DN X o ∧ NoPart o` (`NoPart` excludes only the partial
      matches `npart`, the internal state of the k-ary join); so every other object is exact:
      `clDN_nedge`, `clDN_ninit`, `clDN_nadded`, `clDN_nreq`, `clDN_nvuln`; and `clDN_npart`.
    * The other objects: `clD_link`, `clD_sub`, `clD_pub`, `clD_zsub`, `clD_zpub` (and the same
      for `DR`, `DB`, `DS`; for `DN`: `clDN_link`, `clDN_sub`, `clDN_pub`, `clDN_ndpub`).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.Pipeline
import ApSpec.Backward
import ApSpec.Statics
import ApSpec.ND

namespace ApSpec.PipelineAP
open ApSpec ApSpec.Pipeline

/-! ## 1. Pipeline objects, owners, topics -/

deriving instance DecidableEq for Obj
deriving instance DecidableEq for Call

/-- The pipeline objects over the objects `O` of a closure. -/
inductive PObj (O : Type) where
  /-- an object of the closure; owner: its method -/
  | base (o : O)
  /-- the callee `m` holds the link: added fact `a`, from a caller edge of `M` with premise `ic` -/
  | link (m : MethodId) (a : PFact) (M : MethodId) (ic : PFact)
  /-- the caller's subscription: caller premise `i`, return node `n'`, call `c`, bound fact `a` -/
  | sub  (M : MethodId) (i : PFact) (n' : Node) (c : Call) (a : AFact)
  /-- a published summary edge `j → g` of `m` -/
  | pub  (m : MethodId) (j : PFact) (g : AFact)
  /-- backward run: the zero fact of `M` at the call `c` (return node `n'`) -/
  | zsub (M : MethodId) (n' : Node) (c : Call)
  /-- backward run: a zero-premise summary `zero → g` of `m` -/
  | zpub (m : MethodId) (g : AFact)
deriving DecidableEq

/-- The method of an object of `D`, `DR`, `DB`. -/
def objOwner : Obj → MethodId
  | .init M _ => M
  | .edge M _ _ _ => M
  | .added M _ => M
  | .req M _ _ => M
  | .vuln M _ _ _ => M

/-- The owner of a pipeline object. -/
def PObj.owner {O : Type} (ow : O → MethodId) : PObj O → MethodId
  | .base o => ow o
  | .link m _ _ _ => m
  | .sub M _ _ _ _ => M
  | .pub m _ _ => m
  | .zsub M _ _ => M
  | .zpub m _ => m

def PObj.isSub {O : Type} : PObj O → Bool
  | .sub .. => true
  | .zsub .. => true
  | _ => false

def PObj.isPub {O : Type} : PObj O → Bool
  | .pub .. => true
  | .zpub .. => true
  | _ => false

/-- The topic: the callee of a subscription, the publisher of a publication (and the owner for
    the other objects, which never meet a topic). -/
def PObj.topic {O : Type} (ow : O → MethodId) : PObj O → MethodId
  | .base o => ow o
  | .link m _ _ _ => m
  | .sub _ _ _ c _ => c.callee
  | .pub m _ _ => m
  | .zsub _ _ c => c.callee
  | .zpub m _ => m

/-! ### List helpers -/

section Lists
variable {α : Type} {Q : α → Prop}

theorem all_one {x : α} (h : Q x) : ∀ p ∈ [x], Q p := fun p hp => by
  rw [List.mem_singleton.1 hp]; exact h

theorem all_two {x y : α} (hx : Q x) (hy : Q y) : ∀ p ∈ [x, y], Q p := fun p hp => by
  rcases List.mem_cons.1 hp with rfl | hp
  · exact hx
  · rw [List.mem_singleton.1 hp]; exact hy

theorem fst_of {x : α} {xs : List α} (h : ∀ p ∈ x :: xs, Q p) : Q x := h x List.mem_cons_self

theorem snd_of {x y : α} {xs : List α} (h : ∀ p ∈ x :: y :: xs, Q p) : Q y :=
  h y (List.mem_cons_of_mem _ List.mem_cons_self)

theorem mem_one {x p : α} (h : p ∈ [x]) : p = x := List.mem_singleton.1 h

theorem mem_two {x y p : α} (h : p ∈ [x, y]) : p = x ∨ p = y := by
  rcases List.mem_cons.1 h with h | h
  · exact .inl h
  · exact .inr (List.mem_singleton.1 h)

/-- A one-premise list has one owner. -/
theorem local_one {β : Type} (ow : α → β) {x : α} : ∀ p ∈ [x], ∀ q ∈ [x], ow p = ow q := by
  intro p hp q hq
  rw [mem_one hp, mem_one hq]

/-- A two-premise list has one owner if its two premises have the same owner. -/
theorem local_two {β : Type} (ow : α → β) {x y : α} (h : ow x = ow y) :
    ∀ p ∈ [x, y], ∀ q ∈ [x, y], ow p = ow q := by
  intro p hp q hq
  rcases mem_two hp with rfl | rfl <;> rcases mem_two hq with rfl | rfl
  · rfl
  · exact h
  · exact h.symm
  · rfl

end Lists

/-! ## 2. The rules that `D`, `DR` and `DB` share -/

abbrev PO := PObj Obj

section Common
variable (P : Program) (counted : Acc → Bool) (L : Nat) (sinks : List (MethodId × Node × PFact))

/-- The local rules that the three closures share. -/
inductive CRule : List PO → PO → Prop where
  | start {M i} : CRule [.base (.init M i)] (.base (.edge M i (P.entry M) (startFact i)))
  | step {M i n f n' s f'} : (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transfer counted L s f).facts →
      CRule [.base (.edge M i n f)] (.base (.edge M i n' f'))
  | reqStmt {M i n f n' s t} : (M, n, Instr.stmt s, n') ∈ P.edges →
      t ∈ (transfer counted L s f).reqs →
      CRule [.base (.edge M i n f)] (.base (.req M i t))
  | pass {M i n f n' c} : (M, n, Instr.call c, n') ∈ P.edges →
      memB f.fact.base c.touched = false →
      CRule [.base (.edge M i n f)] (.base (.edge M i n' f))
  /-- the caller sends the link to the callee (a message) -/
  | link {M i n f n' c e a} : (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts →
      CRule [.base (.edge M i n f)] (.link c.callee a.fact M i)
  /-- the callee stores the added fact of a link -/
  | added {m a M ic} : CRule [.link m a M ic] (.base (.added m a))
  /-- the caller subscribes at the call -/
  | sub {M i n f n' c e a} : (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts →
      CRule [.base (.edge M i n f)] (.sub M i n' c a)
  | reqSink {M i n f s t} : (M, n, s) ∈ sinks → check i f s = .request t →
      CRule [.base (.edge M i n f)] (.base (.req M i t))
  | answer {M i t a} : a.mark = .conc t → overlapB a i = true →
      CRule [.base (.req M i t), .base (.added M a)] (.base (.init M (answerInit i a t)))
  /-- the callee climbs a request through a link (the conclusion is a message to the caller) -/
  | reqUp {m j t a M ic} : climbsB a.mark t = true → overlapB a j = true →
      CRule [.base (.req m j t), .link m a M ic] (.base (.req M ic t))
  | vuln {M i n f s} : (M, n, s) ∈ sinks → check i f s = .triggered →
      CRule [.base (.edge M i n f)] (.base (.vuln M n s f.demand))
  | clean {M i n f n' cl f'} : (M, n, Instr.clean cl, n') ∈ P.edges →
      f' ∈ (cleanRes cl f).facts →
      CRule [.base (.edge M i n f)] (.base (.edge M i n' f'))
  | reqClean {M i n f n' cl t} : (M, n, Instr.clean cl, n') ∈ P.edges →
      t ∈ (cleanRes cl f).reqs →
      CRule [.base (.edge M i n f)] (.base (.req M i t))
  | filt {M i n f n' b may} : (M, n, Instr.filt b may, n') ∈ P.edges →
      (f.fact.base = b → may f.fact.path = true) →
      CRule [.base (.edge M i n f)] (.base (.edge M i n' f))

/-- A set of objects closed under the shared rules of the closures. -/
structure Closed (R : Obj → Prop) : Prop where
  start : ∀ {M i}, R (.init M i) → R (.edge M i (P.entry M) (startFact i))
  step : ∀ {M i n f n' s f'}, R (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
    f' ∈ (transfer counted L s f).facts → R (.edge M i n' f')
  reqStmt : ∀ {M i n f n' s t}, R (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
    t ∈ (transfer counted L s f).reqs → R (.req M i t)
  pass : ∀ {M i n f n' c}, R (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
    memB f.fact.base c.touched = false → R (.edge M i n' f)
  added : ∀ {M i n f n' c e a}, R (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
    e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts → R (.added c.callee a.fact)
  reqSink : ∀ {M i n f s t}, R (.edge M i n f) → (M, n, s) ∈ sinks →
    check i f s = .request t → R (.req M i t)
  answer : ∀ {M i t a}, R (.req M i t) → R (.added M a) → a.mark = .conc t →
    overlapB a i = true → R (.init M (answerInit i a t))
  reqUp : ∀ {m j t M ic n f n' c e a}, R (.req m j t) → R (.edge M ic n f) →
    (M, n, Instr.call c, n') ∈ P.edges → c.callee = m → e ∈ c.toCallee →
    a ∈ (applyEdge f e.1 e.2).facts → climbsB a.fact.mark t = true →
    overlapB a.fact j = true → R (.req M ic t)
  vuln : ∀ {M i n f s}, R (.edge M i n f) → (M, n, s) ∈ sinks →
    check i f s = .triggered → R (.vuln M n s f.demand)
  clean : ∀ {M i n f n' cl f'}, R (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
    f' ∈ (cleanRes cl f).facts → R (.edge M i n' f')
  reqClean : ∀ {M i n f n' cl t}, R (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
    t ∈ (cleanRes cl f).reqs → R (.req M i t)
  filt : ∀ {M i n f n' b may}, R (.edge M i n f) → (M, n, Instr.filt b may, n') ∈ P.edges →
    (f.fact.base = b → may f.fact.path = true) → R (.edge M i n' f)

/-- What a link means: a caller edge of `M` with premise `ic`, at a call of `m`, binds a fact
    whose path fact is `a`. (`K` is the premise type: a fact, or a premise list in `DN`.) -/
def LinkOK {K : Type} (E : MethodId → K → Node → AFact → Prop) (m : MethodId) (a : PFact)
    (M : MethodId) (ic : K) : Prop :=
  ∃ (n : Node) (f : AFact) (n' : Node) (c : Call) (e : MicroEdge) (a' : AFact),
    E M ic n f ∧ (M, n, Instr.call c, n') ∈ P.edges ∧ c.callee = m ∧
    e ∈ c.toCallee ∧ a' ∈ (applyEdge f e.1 e.2).facts ∧ a'.fact = a

/-- What a subscription means: a caller edge of `M` with premise `i`, at the call `c` with the
    return node `n'`, binds the fact `a`. -/
def SubOK {K : Type} (E : MethodId → K → Node → AFact → Prop) (M : MethodId) (i : K) (n' : Node)
    (c : Call) (a : AFact) : Prop :=
  ∃ (n : Node) (f : AFact) (e : MicroEdge),
    E M i n f ∧ (M, n, Instr.call c, n') ∈ P.edges ∧ e ∈ c.toCallee ∧
    a ∈ (applyEdge f e.1 e.2).facts

/-- The invariant of a pipeline object: what it means in terms of the closure `R` (with the
    meaning `Pub`, `ZSub`, `ZPub` of the publications and the zero subscriptions). -/
def Inv (R : Obj → Prop) (Pub : MethodId → PFact → AFact → Prop)
    (ZSub : MethodId → Node → Call → Prop) (ZPub : MethodId → AFact → Prop) : PO → Prop
  | .base o => R o
  | .link m a M ic => LinkOK P (fun M i n f => R (.edge M i n f)) m a M ic
  | .sub M i n' c a => SubOK P (fun M i n f => R (.edge M i n f)) M i n' c a
  | .pub m j g => Pub m j g
  | .zsub M n' c => ZSub M n' c
  | .zpub m g => ZPub m g

variable {P counted L sinks}

/-- The shared rules preserve the invariant of every closed set. -/
theorem crule_sound {R : Obj → Prop} {Pub ZSub ZPub} (hR : Closed P counted L sinks R)
    {ps : List PO} {c : PO} (h : CRule P counted L sinks ps c)
    (hps : ∀ p ∈ ps, Inv P R Pub ZSub ZPub p) : Inv P R Pub ZSub ZPub c := by
  cases h with
  | start => exact hR.start (fst_of hps :)
  | step he hf => exact hR.step (fst_of hps :) he hf
  | reqStmt he ht => exact hR.reqStmt (fst_of hps :) he ht
  | pass he hm => exact hR.pass (fst_of hps :) he hm
  | link he he1 ha => exact ⟨_, _, _, _, _, _, (fst_of hps :), he, rfl, he1, ha, rfl⟩
  | added =>
    obtain ⟨_, _, _, _, _, _, hf, he, rfl, he1, ha, rfl⟩ := fst_of hps
    exact hR.added hf he he1 ha
  | sub he he1 ha => exact ⟨_, _, _, (fst_of hps :), he, he1, ha⟩
  | reqSink hs hc => exact hR.reqSink (fst_of hps :) hs hc
  | answer hm hov => exact hR.answer (fst_of hps :) (snd_of hps :) hm hov
  | reqUp hcl hov =>
    obtain ⟨_, _, _, _, _, _, hf, he, hc, he1, ha, rfl⟩ := snd_of hps
    exact hR.reqUp (fst_of hps :) hf he hc he1 ha hcl hov
  | vuln hs hc => exact hR.vuln (fst_of hps :) hs hc
  | clean he hf => exact hR.clean (fst_of hps :) he hf
  | reqClean he ht => exact hR.reqClean (fst_of hps :) he ht
  | filt he hp => exact hR.filt (fst_of hps :) he hp

theorem crule_ne {ps : List PO} {c : PO} (h : CRule P counted L sinks ps c) : ps ≠ [] := by
  cases h <;> exact List.cons_ne_nil _ _

theorem crule_local {ps : List PO} {c : PO} (h : CRule P counted L sinks ps c) :
    ∀ p ∈ ps, ∀ q ∈ ps, p.owner objOwner = q.owner objOwner := by
  cases h with
  | answer => exact local_two _ rfl
  | reqUp => exact local_two _ rfl
  | start => exact local_one _
  | step => exact local_one _
  | reqStmt => exact local_one _
  | pass => exact local_one _
  | link => exact local_one _
  | added => exact local_one _
  | sub => exact local_one _
  | reqSink => exact local_one _
  | vuln => exact local_one _
  | clean => exact local_one _
  | reqClean => exact local_one _
  | filt => exact local_one _

end Common

/-- The roots of a run: the zero fact of each root method. -/
def rootsOf (roots : List MethodId) : List PO := roots.map (fun M => .base (.init M zeroFact))

theorem mem_rootsOf {roots : List MethodId} {x : PO} (h : x ∈ rootsOf roots) :
    ∃ M, M ∈ roots ∧ x = .base (.init M zeroFact) := by
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1 h
  exact ⟨M, hM, rfl⟩

theorem root_mem_rootsOf {roots : List MethodId} {M : MethodId} (h : M ∈ roots) :
    (.base (.init M zeroFact) : PO) ∈ rootsOf roots :=
  List.mem_map.2 ⟨M, h, rfl⟩

/-! ## 3. Run 1: the closure `D` -/

section SysD
variable (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- The local rules of `D`. -/
inductive RuleD : List PO → PO → Prop where
  | common {ps c} : CRule P counted L sinks ps c → RuleD ps c
  | initA {m a} : RuleD [.base (.added m a)] (.base (.init m (α m a)))
  /-- the callee publishes a summary edge -/
  | pub {m j g} : RuleD [.base (.init m j), .base (.edge m j (P.exit m) g)] (.pub m j g)

/-- The join of `D` (the rule `ret`). -/
inductive JoinD : List PO → PO → PO → Prop where
  | ret {M i n' c a j g r e2 r'} : applicable j a.fact = true →
      r ∈ (applySummary a j g).facts → e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      JoinD [.sub M i n' c a] (.pub c.callee j g) (.base (.edge M i n' (limitF counted L r')))

/-- Run 1 as a pipeline system. -/
def sysD : Sys PO MethodId MethodId where
  owner := PObj.owner objOwner
  roots := rootsOf roots
  rule  := RuleD P counted L α sinks
  isSub := PObj.isSub
  isPub := PObj.isPub
  topic := PObj.topic objOwner
  join  := JoinD counted L

/-- What a publication of `D` means. -/
def PubD (m : MethodId) (j : PFact) (g : AFact) : Prop :=
  D P counted L α sinks roots (.init m j) ∧ D P counted L α sinks roots (.edge m j (P.exit m) g)

/-- The invariant of `sysD`. -/
abbrev InvD : PO → Prop :=
  Inv P (D P counted L α sinks roots) (PubD P counted L α sinks roots)
    (fun _ _ _ => False) (fun _ _ => False)

variable {P counted L α sinks roots}

theorem closedD : Closed P counted L sinks (D P counted L α sinks roots) where
  start := D.start
  step := D.step
  reqStmt := D.reqStmt
  pass := D.pass
  added := D.added
  reqSink := D.reqSink
  answer := D.answer
  reqUp := D.reqUp
  vuln := D.vuln
  clean := D.clean
  reqClean := D.reqClean
  filt := D.filt

/-- `sysD` is well formed. -/
theorem sysD_wf : (sysD P counted L α sinks roots).WF where
  rule_ne := by
    intro ps c h
    cases h with
    | common h => exact crule_ne h
    | initA => exact List.cons_ne_nil _ _
    | pub => exact List.cons_ne_nil _ _
  rule_local := by
    intro ps c h
    cases h with
    | common h => exact crule_local h
    | initA => exact local_one _
    | pub => exact local_two _ rfl
  join_ne := by
    intro ss p c h
    cases h
    exact List.cons_ne_nil _ _
  join_sub := by
    intro ss p c h
    cases h
    intro s hs
    rw [mem_one hs]
    exact ⟨rfl, rfl⟩
  join_pub := by
    intro ss p c h
    cases h
    rfl
  join_owner := by
    intro ss p c h
    cases h
    exact local_one _

/-- Soundness: every object of the pipeline closure satisfies its invariant. -/
theorem inv_of_clD {x : PO} (h : Cl (sysD P counted L α sinks roots) x) :
    InvD P counted L α sinks roots x := by
  induction h with
  | root hx =>
    obtain ⟨M, hM, rfl⟩ := mem_rootsOf hx
    exact D.root hM
  | rule hr _ ih =>
    cases hr with
    | common h => exact crule_sound closedD h ih
    | initA => exact D.initA (fst_of ih :)
    | pub => exact ⟨(fst_of ih :), (snd_of ih :)⟩
  | join hj _ _ ihs ihp =>
    cases hj with
    | ret hap hr he2 hr' =>
      obtain ⟨_, _, _, hf, he, he1, ha⟩ := fst_of ihs
      exact D.ret hf he he1 ha ihp.1 hap ihp.2 hr he2 hr'

/-- Completeness: every object of `D` is in the pipeline closure. -/
theorem cl_of_D {o : Obj} (h : D P counted L α sinks roots o) :
    Cl (sysD P counted L α sinks roots) (.base o) := by
  induction h with
  | root hM => exact Cl.root (root_mem_rootsOf hM)
  | start _ ih => exact Cl.rule (RuleD.common CRule.start) (all_one ih)
  | step _ he hf ih => exact Cl.rule (RuleD.common (CRule.step he hf)) (all_one ih)
  | reqStmt _ he ht ih => exact Cl.rule (RuleD.common (CRule.reqStmt he ht)) (all_one ih)
  | pass _ he hm ih => exact Cl.rule (RuleD.common (CRule.pass he hm)) (all_one ih)
  | added _ he he1 ha ih =>
    exact Cl.rule (RuleD.common CRule.added)
      (all_one (Cl.rule (RuleD.common (CRule.link he he1 ha)) (all_one ih)))
  | initA _ ih => exact Cl.rule RuleD.initA (all_one ih)
  | ret _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    exact Cl.join (JoinD.ret hap hr he2 hr')
      (all_one (Cl.rule (RuleD.common (CRule.sub he he1 ha)) (all_one ihf)))
      (Cl.rule RuleD.pub (all_two ihj ihg))
  | reqSink _ hs hc ih => exact Cl.rule (RuleD.common (CRule.reqSink hs hc)) (all_one ih)
  | answer _ _ hm hov ihr iha => exact Cl.rule (RuleD.common (CRule.answer hm hov)) (all_two ihr iha)
  | reqUp _ _ he hc he1 ha hcl hov ihr ihf =>
    subst hc
    exact Cl.rule (RuleD.common (CRule.reqUp hcl hov))
      (all_two ihr (Cl.rule (RuleD.common (CRule.link he he1 ha)) (all_one ihf)))
  | vuln _ hs hc ih => exact Cl.rule (RuleD.common (CRule.vuln hs hc)) (all_one ih)
  | clean _ he hf ih => exact Cl.rule (RuleD.common (CRule.clean he hf)) (all_one ih)
  | reqClean _ he ht ih => exact Cl.rule (RuleD.common (CRule.reqClean he ht)) (all_one ih)
  | filt _ he hp ih => exact Cl.rule (RuleD.common (CRule.filt he hp)) (all_one ih)

/-- THE THEOREM for run 1: the pipeline closure on the closure objects is exactly `D`. -/
theorem clD_iff {o : Obj} :
    Cl (sysD P counted L α sinks roots) (.base o) ↔ D P counted L α sinks roots o :=
  ⟨fun h => inv_of_clD h, cl_of_D⟩

theorem clD_link {m : MethodId} {a : PFact} {M : MethodId} {ic : PFact} :
    Cl (sysD P counted L α sinks roots) (.link m a M ic) ↔
      LinkOK P (fun M i n f => D P counted L α sinks roots (.edge M i n f)) m a M ic := by
  refine ⟨fun h => inv_of_clD h, ?_⟩
  rintro ⟨_, _, _, _, _, _, hf, he, rfl, he1, ha, rfl⟩
  exact Cl.rule (RuleD.common (CRule.link he he1 ha)) (all_one (cl_of_D hf))

theorem clD_sub {M : MethodId} {i : PFact} {n' : Node} {c : Call} {a : AFact} :
    Cl (sysD P counted L α sinks roots) (.sub M i n' c a) ↔
      SubOK P (fun M i n f => D P counted L α sinks roots (.edge M i n f)) M i n' c a := by
  refine ⟨fun h => inv_of_clD h, ?_⟩
  rintro ⟨_, _, _, hf, he, he1, ha⟩
  exact Cl.rule (RuleD.common (CRule.sub he he1 ha)) (all_one (cl_of_D hf))

theorem clD_pub {m : MethodId} {j : PFact} {g : AFact} :
    Cl (sysD P counted L α sinks roots) (.pub m j g) ↔
      D P counted L α sinks roots (.init m j) ∧
        D P counted L α sinks roots (.edge m j (P.exit m) g) := by
  refine ⟨fun h => inv_of_clD h, ?_⟩
  rintro ⟨hj, hg⟩
  exact Cl.rule RuleD.pub (all_two (cl_of_D hj) (cl_of_D hg))

theorem clD_zsub {M : MethodId} {n' : Node} {c : Call} :
    ¬ Cl (sysD P counted L α sinks roots) (.zsub M n' c) := fun h => inv_of_clD h

theorem clD_zpub {m : MethodId} {g : AFact} :
    ¬ Cl (sysD P counted L α sinks roots) (.zpub m g) := fun h => inv_of_clD h

end SysD

/-! ## 4. The restricted runs: the closure `DR` -/

section SysDR
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → (PFact × AFact) → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- The local rules of a restricted run (also the forward-shaped rules of the backward run). -/
inductive RuleR : List PO → PO → Prop where
  | common {ps c} : CRule P counted L sinks ps c → RuleR ps c
  | initR {m a d j} : demand m d → emit d.din a = some j →
      RuleR [.base (.added m a)] (.base (.init m j))
  /-- a persisted record: a fixed predicate, so the rule is local at the caller -/
  | retRec {M i n f n' c e1 a j g r e2 r'} : (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      recs c.callee (j, g) → (sat j a.fact = true ∨ applicable j a.fact = true) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      RuleR [.base (.edge M i n f)] (.base (.edge M i n' (limitF counted L r')))
  /-- the callee restricts a summary edge by one of its demand edges and publishes the result -/
  | pub {m j g d g'} : demand m d → restrict j g d = some g' →
      RuleR [.base (.init m j), .base (.edge m j (P.exit m) g)] (.pub m j g')

/-- The join of a restricted run (the rule `ret`). -/
inductive JoinR : List PO → PO → PO → Prop where
  | ret {M i n' c a j g r e2 r'} : sat j a.fact = true →
      r ∈ (applySummary a j g).facts → e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      JoinR [.sub M i n' c a] (.pub c.callee j g) (.base (.edge M i n' (limitF counted L r')))

/-- A restricted run as a pipeline system. -/
def sysDR : Sys PO MethodId MethodId where
  owner := PObj.owner objOwner
  roots := rootsOf roots
  rule  := RuleR P counted L demand emit sat restrict recs sinks
  isSub := PObj.isSub
  isPub := PObj.isPub
  topic := PObj.topic objOwner
  join  := JoinR counted L sat

/-- What a publication of a restricted run means: a summary edge of `m`, restricted by a demand
    edge of `m`. -/
def PubR (R : Obj → Prop) (m : MethodId) (j : PFact) (g' : AFact) : Prop :=
  ∃ (g : AFact) (d : DemandEdge), R (.init m j) ∧ R (.edge m j (P.exit m) g) ∧ demand m d ∧
    restrict j g d = some g'

/-- A set of objects closed under the rules of a restricted run (other than the root). -/
structure ClosedR (R : Obj → Prop) : Prop where
  base : Closed P counted L sinks R
  initR : ∀ {m a d j}, R (.added m a) → demand m d → emit d.din a = some j → R (.init m j)
  retRec : ∀ {M i n f n' c e1 a j g r e2 r'}, R (.edge M i n f) →
    (M, n, Instr.call c, n') ∈ P.edges → e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
    recs c.callee (j, g) → (sat j a.fact = true ∨ applicable j a.fact = true) →
    r ∈ (applySummary a j g).facts → e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
    R (.edge M i n' (limitF counted L r'))
  ret : ∀ {M i n f n' c e1 a j g d g' r e2 r'}, R (.edge M i n f) →
    (M, n, Instr.call c, n') ∈ P.edges → e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
    R (.init c.callee j) → R (.edge c.callee j (P.exit c.callee) g) →
    demand c.callee d → restrict j g d = some g' → sat j a.fact = true →
    r ∈ (applySummary a j g').facts → e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
    R (.edge M i n' (limitF counted L r'))

/-- The invariant of `sysDR`. -/
abbrev InvDR : PO → Prop :=
  Inv P (DR P counted L demand emit sat restrict recs sinks roots)
    (PubR P demand restrict (DR P counted L demand emit sat restrict recs sinks roots))
    (fun _ _ _ => False) (fun _ _ => False)

variable {P counted L demand emit sat restrict recs sinks roots}

theorem ruleR_sound {R : Obj → Prop} {ZSub ZPub}
    (hR : ClosedR P counted L demand emit sat restrict recs sinks R)
    {ps : List PO} {c : PO} (h : RuleR P counted L demand emit sat restrict recs sinks ps c)
    (hps : ∀ p ∈ ps, Inv P R (PubR P demand restrict R) ZSub ZPub p) :
    Inv P R (PubR P demand restrict R) ZSub ZPub c := by
  cases h with
  | common h => exact crule_sound hR.base h hps
  | initR hd he => exact hR.initR (fst_of hps :) hd he
  | retRec he he1 ha hrec hs hr he2 hr' =>
    exact hR.retRec (fst_of hps :) he he1 ha hrec hs hr he2 hr'
  | pub hd hres => exact ⟨_, _, (fst_of hps :), (snd_of hps :), hd, hres⟩

theorem joinR_sound {R : Obj → Prop} {ZSub ZPub}
    (hR : ClosedR P counted L demand emit sat restrict recs sinks R)
    {ss : List PO} {p c : PO} (h : JoinR counted L sat ss p c)
    (hss : ∀ s ∈ ss, Inv P R (PubR P demand restrict R) ZSub ZPub s)
    (hp : Inv P R (PubR P demand restrict R) ZSub ZPub p) :
    Inv P R (PubR P demand restrict R) ZSub ZPub c := by
  cases h with
  | ret hs hr he2 hr' =>
    obtain ⟨_, _, _, hf, he, he1, ha⟩ := (fst_of hss :)
    obtain ⟨_, _, hj, hg, hd, hres⟩ := hp
    exact hR.ret hf he he1 ha hj hg hd hres hs hr he2 hr'

theorem ruleR_ne {ps : List PO} {c : PO}
    (h : RuleR P counted L demand emit sat restrict recs sinks ps c) : ps ≠ [] := by
  cases h with
  | common h => exact crule_ne h
  | initR => exact List.cons_ne_nil _ _
  | retRec => exact List.cons_ne_nil _ _
  | pub => exact List.cons_ne_nil _ _

theorem ruleR_local {ps : List PO} {c : PO}
    (h : RuleR P counted L demand emit sat restrict recs sinks ps c) :
    ∀ p ∈ ps, ∀ q ∈ ps, p.owner objOwner = q.owner objOwner := by
  cases h with
  | common h => exact crule_local h
  | initR => exact local_one _
  | retRec => exact local_one _
  | pub => exact local_two _ rfl

theorem joinR_shape {ss : List PO} {p c : PO} (h : JoinR counted L sat ss p c) :
    ss ≠ [] ∧ (∀ s ∈ ss, s.isSub = true ∧ s.topic objOwner = p.topic objOwner) ∧
      p.isPub = true ∧ (∀ s ∈ ss, ∀ s' ∈ ss, s.owner objOwner = s'.owner objOwner) := by
  cases h
  refine ⟨List.cons_ne_nil _ _, ?_, rfl, local_one _⟩
  intro s hs
  rw [mem_one hs]
  exact ⟨rfl, rfl⟩

theorem closedDR : ClosedR P counted L demand emit sat restrict recs sinks
    (DR P counted L demand emit sat restrict recs sinks roots) where
  base :=
    { start := DR.start, step := DR.step, reqStmt := DR.reqStmt, pass := DR.pass,
      added := DR.added, reqSink := DR.reqSink, answer := DR.answer, reqUp := DR.reqUp,
      vuln := DR.vuln, clean := DR.clean, reqClean := DR.reqClean, filt := DR.filt }
  initR := DR.initR
  retRec := DR.retRec
  ret := DR.ret

/-- `sysDR` is well formed. -/
theorem sysDR_wf : (sysDR P counted L demand emit sat restrict recs sinks roots).WF where
  rule_ne := fun _ _ h => ruleR_ne h
  rule_local := fun _ _ h => ruleR_local h
  join_ne := fun _ _ _ h => (joinR_shape h).1
  join_sub := fun _ _ _ h => (joinR_shape h).2.1
  join_pub := fun _ _ _ h => (joinR_shape h).2.2.1
  join_owner := fun _ _ _ h => (joinR_shape h).2.2.2

theorem inv_of_clDR {x : PO} (h : Cl (sysDR P counted L demand emit sat restrict recs sinks roots) x) :
    InvDR P counted L demand emit sat restrict recs sinks roots x := by
  induction h with
  | root hx =>
    obtain ⟨M, hM, rfl⟩ := mem_rootsOf hx
    exact DR.root hM
  | rule hr _ ih => exact ruleR_sound closedDR hr ih
  | join hj _ _ ihs ihp => exact joinR_sound closedDR hj ihs ihp

theorem cl_of_DR {o : Obj} (h : DR P counted L demand emit sat restrict recs sinks roots o) :
    Cl (sysDR P counted L demand emit sat restrict recs sinks roots) (.base o) := by
  induction h with
  | root hM => exact Cl.root (root_mem_rootsOf hM)
  | start _ ih => exact Cl.rule (RuleR.common CRule.start) (all_one ih)
  | step _ he hf ih => exact Cl.rule (RuleR.common (CRule.step he hf)) (all_one ih)
  | reqStmt _ he ht ih => exact Cl.rule (RuleR.common (CRule.reqStmt he ht)) (all_one ih)
  | pass _ he hm ih => exact Cl.rule (RuleR.common (CRule.pass he hm)) (all_one ih)
  | added _ he he1 ha ih =>
    exact Cl.rule (RuleR.common CRule.added)
      (all_one (Cl.rule (RuleR.common (CRule.link he he1 ha)) (all_one ih)))
  | initR _ hd he ih => exact Cl.rule (RuleR.initR hd he) (all_one ih)
  | ret _ he he1 ha _ _ hd hres hs hr he2 hr' ihf ihj ihg =>
    exact Cl.join (JoinR.ret hs hr he2 hr')
      (all_one (Cl.rule (RuleR.common (CRule.sub he he1 ha)) (all_one ihf)))
      (Cl.rule (RuleR.pub hd hres) (all_two ihj ihg))
  | retRec _ he he1 ha hrec hs hr he2 hr' ih =>
    exact Cl.rule (RuleR.retRec he he1 ha hrec hs hr he2 hr') (all_one ih)
  | reqSink _ hs hc ih => exact Cl.rule (RuleR.common (CRule.reqSink hs hc)) (all_one ih)
  | answer _ _ hm hov ihr iha =>
    exact Cl.rule (RuleR.common (CRule.answer hm hov)) (all_two ihr iha)
  | reqUp _ _ he hc he1 ha hcl hov ihr ihf =>
    subst hc
    exact Cl.rule (RuleR.common (CRule.reqUp hcl hov))
      (all_two ihr (Cl.rule (RuleR.common (CRule.link he he1 ha)) (all_one ihf)))
  | vuln _ hs hc ih => exact Cl.rule (RuleR.common (CRule.vuln hs hc)) (all_one ih)
  | clean _ he hf ih => exact Cl.rule (RuleR.common (CRule.clean he hf)) (all_one ih)
  | reqClean _ he ht ih => exact Cl.rule (RuleR.common (CRule.reqClean he ht)) (all_one ih)
  | filt _ he hp ih => exact Cl.rule (RuleR.common (CRule.filt he hp)) (all_one ih)

/-- THE THEOREM for a restricted run: the pipeline closure on the closure objects is exactly
    `DR`. -/
theorem clDR_iff {o : Obj} :
    Cl (sysDR P counted L demand emit sat restrict recs sinks roots) (.base o) ↔
      DR P counted L demand emit sat restrict recs sinks roots o :=
  ⟨fun h => inv_of_clDR h, cl_of_DR⟩

theorem clDR_link {m : MethodId} {a : PFact} {M : MethodId} {ic : PFact} :
    Cl (sysDR P counted L demand emit sat restrict recs sinks roots) (.link m a M ic) ↔
      LinkOK P (fun M i n f => DR P counted L demand emit sat restrict recs sinks roots
        (.edge M i n f)) m a M ic := by
  refine ⟨fun h => inv_of_clDR h, ?_⟩
  rintro ⟨_, _, _, _, _, _, hf, he, rfl, he1, ha, rfl⟩
  exact Cl.rule (RuleR.common (CRule.link he he1 ha)) (all_one (cl_of_DR hf))

theorem clDR_sub {M : MethodId} {i : PFact} {n' : Node} {c : Call} {a : AFact} :
    Cl (sysDR P counted L demand emit sat restrict recs sinks roots) (.sub M i n' c a) ↔
      SubOK P (fun M i n f => DR P counted L demand emit sat restrict recs sinks roots
        (.edge M i n f)) M i n' c a := by
  refine ⟨fun h => inv_of_clDR h, ?_⟩
  rintro ⟨_, _, _, hf, he, he1, ha⟩
  exact Cl.rule (RuleR.common (CRule.sub he he1 ha)) (all_one (cl_of_DR hf))

theorem clDR_pub {m : MethodId} {j : PFact} {g' : AFact} :
    Cl (sysDR P counted L demand emit sat restrict recs sinks roots) (.pub m j g') ↔
      ∃ (g : AFact) (d : DemandEdge),
        DR P counted L demand emit sat restrict recs sinks roots (.init m j) ∧
        DR P counted L demand emit sat restrict recs sinks roots (.edge m j (P.exit m) g) ∧
        demand m d ∧ restrict j g d = some g' := by
  refine ⟨fun h => inv_of_clDR h, ?_⟩
  rintro ⟨_, _, hj, hg, hd, hres⟩
  exact Cl.rule (RuleR.pub hd hres) (all_two (cl_of_DR hj) (cl_of_DR hg))

theorem clDR_zsub {M : MethodId} {n' : Node} {c : Call} :
    ¬ Cl (sysDR P counted L demand emit sat restrict recs sinks roots) (.zsub M n' c) :=
  fun h => inv_of_clDR h

theorem clDR_zpub {m : MethodId} {g : AFact} :
    ¬ Cl (sysDR P counted L demand emit sat restrict recs sinks roots) (.zpub m g) :=
  fun h => inv_of_clDR h

end SysDR

/-! ## 5. The backward run: the closure `DB` -/

section SysDB
open ApSpec.Backward
variable (Pb : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → (PFact × AFact) → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)
  (seeds : List (MethodId × Node × PFact))
  (zbind : Bool)

/-- The local rules of the backward run: the rules of a restricted run on the reversed program,
    and the zero rules. -/
inductive RuleB : List PO → PO → Prop where
  | fwd {ps c} : RuleR Pb counted L demand emit sat restrict recs sinks ps c → RuleB ps c
  | zpass {M n n' c} : (M, n, Instr.call c, n') ∈ Pb.edges →
      RuleB [.base (.edge M zeroFact n zeroAF)] (.base (.edge M zeroFact n' zeroAF))
  /-- the zero fact enters the callee: a message to the callee -/
  | zin {M n n' c} : zbind = true → (M, n, Instr.call c, n') ∈ Pb.edges →
      RuleB [.base (.edge M zeroFact n zeroAF)] (.base (.init c.callee zeroFact))
  | seed {M n s} : (M, n, s) ∈ seeds →
      RuleB [.base (.edge M zeroFact n zeroAF)]
        (.base (.edge M zeroFact n (limitF counted L ⟨s, false⟩)))
  /-- the caller subscribes its zero fact at the call -/
  | zsub {M n n' c} : zbind = true → (M, n, Instr.call c, n') ∈ Pb.edges →
      RuleB [.base (.edge M zeroFact n zeroAF)] (.zsub M n' c)
  /-- the callee publishes a zero-premise summary (not restricted) -/
  | zpub {m g} : RuleB [.base (.edge m zeroFact (Pb.exit m) g)] (.zpub m g)

/-- The joins of the backward run: `ret` and the balanced return `zret`. -/
inductive JoinB : List PO → PO → PO → Prop where
  | fwd {ss p c} : JoinR counted L sat ss p c → JoinB ss p c
  | zret {M n' c g r e2 r'} : r ∈ (applySummary zeroAF zeroFact g).facts → e2 ∈ c.fromCallee →
      r' ∈ (applyEdge r e2.1 e2.2).facts →
      JoinB [.zsub M n' c] (.zpub c.callee g) (.base (.edge M zeroFact n' (limitF counted L r')))

/-- The backward run as a pipeline system. -/
def sysDB : Sys PO MethodId MethodId where
  owner := PObj.owner objOwner
  roots := rootsOf roots
  rule  := RuleB Pb counted L demand emit sat restrict recs sinks seeds zbind
  isSub := PObj.isSub
  isPub := PObj.isPub
  topic := PObj.topic objOwner
  join  := JoinB counted L sat

/-- What a zero subscription means. -/
def ZSubOK (R : Obj → Prop) (M : MethodId) (n' : Node) (c : Call) : Prop :=
  zbind = true ∧ ∃ n : Node, R (.edge M zeroFact n zeroAF) ∧ (M, n, Instr.call c, n') ∈ Pb.edges

/-- What a zero publication means. -/
def ZPubOK (R : Obj → Prop) (m : MethodId) (g : AFact) : Prop :=
  R (.edge m zeroFact (Pb.exit m) g)

/-- The invariant of `sysDB`. -/
abbrev InvDB : PO → Prop :=
  let R := DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind
  Inv Pb R (PubR Pb demand restrict R) (ZSubOK Pb zbind R) (ZPubOK Pb R)

variable {Pb counted L demand emit sat restrict recs sinks roots seeds zbind}

theorem closedDB : ClosedR Pb counted L demand emit sat restrict recs sinks
    (DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind) where
  base :=
    { start := DB.start, step := DB.step, reqStmt := DB.reqStmt, pass := DB.pass,
      added := DB.added, reqSink := DB.reqSink, answer := DB.answer, reqUp := DB.reqUp,
      vuln := DB.vuln, clean := DB.clean, reqClean := DB.reqClean, filt := DB.filt }
  initR := DB.initR
  retRec := DB.retRec
  ret := DB.ret

/-- `sysDB` is well formed. -/
theorem sysDB_wf :
    (sysDB Pb counted L demand emit sat restrict recs sinks roots seeds zbind).WF where
  rule_ne := by
    intro ps c h
    cases h with
    | fwd h => exact ruleR_ne h
    | _ => exact List.cons_ne_nil _ _
  rule_local := by
    intro ps c h
    cases h with
    | fwd h => exact ruleR_local h
    | _ => exact local_one _
  join_ne := by
    intro ss p c h
    cases h with
    | fwd h => exact (joinR_shape h).1
    | zret => exact List.cons_ne_nil _ _
  join_sub := by
    intro ss p c h
    cases h with
    | fwd h => exact (joinR_shape h).2.1
    | zret =>
      intro s hs
      rw [mem_one hs]
      exact ⟨rfl, rfl⟩
  join_pub := by
    intro ss p c h
    cases h with
    | fwd h => exact (joinR_shape h).2.2.1
    | zret => rfl
  join_owner := by
    intro ss p c h
    cases h with
    | fwd h => exact (joinR_shape h).2.2.2
    | zret => exact local_one _

theorem inv_of_clDB {x : PO}
    (h : Cl (sysDB Pb counted L demand emit sat restrict recs sinks roots seeds zbind) x) :
    InvDB Pb counted L demand emit sat restrict recs sinks roots seeds zbind x := by
  induction h with
  | root hx =>
    obtain ⟨M, hM, rfl⟩ := mem_rootsOf hx
    exact DB.root hM
  | rule hr _ ih =>
    cases hr with
    | fwd h => exact ruleR_sound closedDB h ih
    | zpass he => exact DB.zpass (fst_of ih :) he
    | zin hz he => exact DB.zin hz (fst_of ih :) he
    | seed hs => exact DB.seed hs (fst_of ih :)
    | zsub hz he => exact ⟨hz, _, (fst_of ih :), he⟩
    | zpub => exact (fst_of ih :)
  | join hj _ _ ihs ihp =>
    cases hj with
    | fwd h => exact joinR_sound closedDB h ihs ihp
    | zret hr he2 hr' =>
      obtain ⟨hz, _, hf, he⟩ := (fst_of ihs :)
      exact DB.zret hz hf he ihp hr he2 hr'

theorem cl_of_DB {o : Obj}
    (h : DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind o) :
    Cl (sysDB Pb counted L demand emit sat restrict recs sinks roots seeds zbind) (.base o) := by
  induction h with
  | root hM => exact Cl.root (root_mem_rootsOf hM)
  | start _ ih => exact Cl.rule (RuleB.fwd (RuleR.common CRule.start)) (all_one ih)
  | step _ he hf ih => exact Cl.rule (RuleB.fwd (RuleR.common (CRule.step he hf))) (all_one ih)
  | reqStmt _ he ht ih =>
    exact Cl.rule (RuleB.fwd (RuleR.common (CRule.reqStmt he ht))) (all_one ih)
  | pass _ he hm ih => exact Cl.rule (RuleB.fwd (RuleR.common (CRule.pass he hm))) (all_one ih)
  | added _ he he1 ha ih =>
    exact Cl.rule (RuleB.fwd (RuleR.common CRule.added))
      (all_one (Cl.rule (RuleB.fwd (RuleR.common (CRule.link he he1 ha))) (all_one ih)))
  | initR _ hd he ih => exact Cl.rule (RuleB.fwd (RuleR.initR hd he)) (all_one ih)
  | ret _ he he1 ha _ _ hd hres hs hr he2 hr' ihf ihj ihg =>
    exact Cl.join (JoinB.fwd (JoinR.ret hs hr he2 hr'))
      (all_one (Cl.rule (RuleB.fwd (RuleR.common (CRule.sub he he1 ha))) (all_one ihf)))
      (Cl.rule (RuleB.fwd (RuleR.pub hd hres)) (all_two ihj ihg))
  | retRec _ he he1 ha hrec hs hr he2 hr' ih =>
    exact Cl.rule (RuleB.fwd (RuleR.retRec he he1 ha hrec hs hr he2 hr')) (all_one ih)
  | reqSink _ hs hc ih =>
    exact Cl.rule (RuleB.fwd (RuleR.common (CRule.reqSink hs hc))) (all_one ih)
  | answer _ _ hm hov ihr iha =>
    exact Cl.rule (RuleB.fwd (RuleR.common (CRule.answer hm hov))) (all_two ihr iha)
  | reqUp _ _ he hc he1 ha hcl hov ihr ihf =>
    subst hc
    exact Cl.rule (RuleB.fwd (RuleR.common (CRule.reqUp hcl hov)))
      (all_two ihr (Cl.rule (RuleB.fwd (RuleR.common (CRule.link he he1 ha))) (all_one ihf)))
  | vuln _ hs hc ih => exact Cl.rule (RuleB.fwd (RuleR.common (CRule.vuln hs hc))) (all_one ih)
  | clean _ he hf ih => exact Cl.rule (RuleB.fwd (RuleR.common (CRule.clean he hf))) (all_one ih)
  | reqClean _ he ht ih =>
    exact Cl.rule (RuleB.fwd (RuleR.common (CRule.reqClean he ht))) (all_one ih)
  | filt _ he hp ih => exact Cl.rule (RuleB.fwd (RuleR.common (CRule.filt he hp))) (all_one ih)
  | zpass _ he ih => exact Cl.rule (RuleB.zpass he) (all_one ih)
  | zin hz _ he ih => exact Cl.rule (RuleB.zin hz he) (all_one ih)
  | seed hs _ ih => exact Cl.rule (RuleB.seed hs) (all_one ih)
  | zret hz _ he _ hr he2 hr' ihf ihg =>
    exact Cl.join (JoinB.zret hr he2 hr') (all_one (Cl.rule (RuleB.zsub hz he) (all_one ihf)))
      (Cl.rule RuleB.zpub (all_one ihg))

/-- THE THEOREM for the backward run: the pipeline closure on the closure objects is exactly
    `DB`. -/
theorem clDB_iff {o : Obj} :
    Cl (sysDB Pb counted L demand emit sat restrict recs sinks roots seeds zbind) (.base o) ↔
      DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind o :=
  ⟨fun h => inv_of_clDB h, cl_of_DB⟩

theorem clDB_link {m : MethodId} {a : PFact} {M : MethodId} {ic : PFact} :
    Cl (sysDB Pb counted L demand emit sat restrict recs sinks roots seeds zbind)
        (.link m a M ic) ↔
      LinkOK Pb (fun M i n f => DB Pb counted L demand emit sat restrict recs sinks roots seeds
        zbind (.edge M i n f)) m a M ic := by
  refine ⟨fun h => inv_of_clDB h, ?_⟩
  rintro ⟨_, _, _, _, _, _, hf, he, rfl, he1, ha, rfl⟩
  exact Cl.rule (RuleB.fwd (RuleR.common (CRule.link he he1 ha))) (all_one (cl_of_DB hf))

theorem clDB_sub {M : MethodId} {i : PFact} {n' : Node} {c : Call} {a : AFact} :
    Cl (sysDB Pb counted L demand emit sat restrict recs sinks roots seeds zbind)
        (.sub M i n' c a) ↔
      SubOK Pb (fun M i n f => DB Pb counted L demand emit sat restrict recs sinks roots seeds
        zbind (.edge M i n f)) M i n' c a := by
  refine ⟨fun h => inv_of_clDB h, ?_⟩
  rintro ⟨_, _, _, hf, he, he1, ha⟩
  exact Cl.rule (RuleB.fwd (RuleR.common (CRule.sub he he1 ha))) (all_one (cl_of_DB hf))

theorem clDB_pub {m : MethodId} {j : PFact} {g' : AFact} :
    Cl (sysDB Pb counted L demand emit sat restrict recs sinks roots seeds zbind) (.pub m j g') ↔
      ∃ (g : AFact) (d : DemandEdge),
        DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind (.init m j) ∧
        DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind
          (.edge m j (Pb.exit m) g) ∧
        demand m d ∧ restrict j g d = some g' := by
  refine ⟨fun h => inv_of_clDB h, ?_⟩
  rintro ⟨_, _, hj, hg, hd, hres⟩
  exact Cl.rule (RuleB.fwd (RuleR.pub hd hres)) (all_two (cl_of_DB hj) (cl_of_DB hg))

theorem clDB_zsub {M : MethodId} {n' : Node} {c : Call} :
    Cl (sysDB Pb counted L demand emit sat restrict recs sinks roots seeds zbind) (.zsub M n' c) ↔
      zbind = true ∧ ∃ n : Node,
        DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind
          (.edge M zeroFact n zeroAF) ∧ (M, n, Instr.call c, n') ∈ Pb.edges := by
  refine ⟨fun h => inv_of_clDB h, ?_⟩
  rintro ⟨hz, _, hf, he⟩
  exact Cl.rule (RuleB.zsub hz he) (all_one (cl_of_DB hf))

theorem clDB_zpub {m : MethodId} {g : AFact} :
    Cl (sysDB Pb counted L demand emit sat restrict recs sinks roots seeds zbind) (.zpub m g) ↔
      DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind
        (.edge m zeroFact (Pb.exit m) g) := by
  refine ⟨fun h => inv_of_clDB h, ?_⟩
  intro hg
  exact Cl.rule RuleB.zpub (all_one (cl_of_DB hg))

end SysDB

/-! ## 6. Run 1 with the static rule: the closure `Statics.DS`

The objects are `PObj SObj`. The position request climbs like a mark request (`sreqUp`: local
at the callee, through the link; its condition `climbOK ic a p` reads the caller premise and
the bound fact, both in the link). The overlap reading `sret` is a second join of the same
subscription and publication as `ret` (its condition `fbOK i a j` reads the caller premise and
the bound fact, in the subscription, and the callee premise, in the publication). -/

section SysDS
open ApSpec.Statics
variable (X : SCtx)

abbrev PS := PObj SObj

/-- The method of an object of `DS`. -/
def sobjOwner : SObj → MethodId
  | .init M _ => M
  | .edge M _ _ _ => M
  | .added M _ => M
  | .req M _ _ => M
  | .sreq M _ _ => M
  | .vuln M _ _ _ => M

/-- The local rules of `DS`. -/
inductive RuleS : List PS → PS → Prop where
  | start {M i} : RuleS [.base (.init M i)] (.base (.edge M i (X.P.entry M) (startFact i)))
  | step {M i n f n' s f'} : (M, n, Instr.stmt s, n') ∈ X.P.edges →
      f' ∈ (transfer X.counted X.FL (sKeepP (X.fireB i f) s) f).facts →
      RuleS [.base (.edge M i n f)] (.base (.edge M i n' f'))
  | reqStmt {M i n f n' s t} : (M, n, Instr.stmt s, n') ∈ X.P.edges →
      t ∈ (transfer X.counted X.FL (sKeepP (X.fireB i f) s) f).reqs →
      RuleS [.base (.edge M i n f)] (.base (.req M i t))
  | sreqStmt {M i n f n' s e} : (M, n, Instr.stmt s, n') ∈ X.P.edges → e ∈ s.edges →
      X.fireB i f e = true →
      RuleS [.base (.edge M i n f)] (.base (.sreq M i (X.reqP e.1.path)))
  | pass {M i n f n' c} : (M, n, Instr.call c, n') ∈ X.P.edges →
      memB f.fact.base c.touched = false →
      RuleS [.base (.edge M i n f)] (.base (.edge M i n' f))
  | link {M i n f n' c e a} : (M, n, Instr.call c, n') ∈ X.P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts →
      RuleS [.base (.edge M i n f)] (.link c.callee a.fact M i)
  | added {m a M ic} : RuleS [.link m a M ic] (.base (.added m a))
  | initA {m a} : RuleS [.base (.added m a)] (.base (.init m (X.α m a)))
  | sub {M i n f n' c e a} : (M, n, Instr.call c, n') ∈ X.P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts →
      RuleS [.base (.edge M i n f)] (.sub M i n' c a)
  | pub {m j g} : RuleS [.base (.init m j), .base (.edge m j (X.P.exit m) g)] (.pub m j g)
  | reqSink {M i n f s t} : (M, n, s) ∈ X.sinks → check i f s = .request t →
      RuleS [.base (.edge M i n f)] (.base (.req M i t))
  | answer {M i t a} : a.mark = .conc t → overlapB a i = true →
      RuleS [.base (.req M i t), .base (.added M a)] (.base (.init M (X.ansInit i a t)))
  | sanswer {M i p a} : X.ansOK a p = true →
      RuleS [.base (.sreq M i p), .base (.added M a)] (.base (.init M (sAns X.sB p)))
  | reqUp {m j t a M ic} : climbsB a.mark t = true → overlapB a j = true →
      RuleS [.base (.req m j t), .link m a M ic] (.base (.req M ic t))
  /-- the position request climbs at the callee, through the link -/
  | sreqUp {m j p a M ic} : X.climbOK ic a p = true →
      RuleS [.base (.sreq m j p), .link m a M ic] (.base (.sreq M ic p))
  | vuln {M i n f s} : (M, n, s) ∈ X.sinks → check i f s = .triggered →
      RuleS [.base (.edge M i n f)] (.base (.vuln M n s f.demand))
  | clean {M i n f n' cl f'} : (M, n, Instr.clean cl, n') ∈ X.P.edges →
      f' ∈ (cleanRes cl f).facts →
      RuleS [.base (.edge M i n f)] (.base (.edge M i n' f'))
  | reqClean {M i n f n' cl t} : (M, n, Instr.clean cl, n') ∈ X.P.edges →
      t ∈ (cleanRes cl f).reqs →
      RuleS [.base (.edge M i n f)] (.base (.req M i t))
  | filt {M i n f n' b may} : (M, n, Instr.filt b may, n') ∈ X.P.edges →
      (f.fact.base = b → may f.fact.path = true) →
      RuleS [.base (.edge M i n f)] (.base (.edge M i n' f))

/-- The joins of `DS`: `ret` and the overlap reading `sret`. -/
inductive JoinS : List PS → PS → PS → Prop where
  | ret {M i n' c a j g r e2 r'} : applicable j a.fact = true →
      r ∈ (applySummary a j g).facts → e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      JoinS [.sub M i n' c a] (.pub c.callee j g) (.base (.edge M i n' (limitF X.counted X.FL r')))
  | sret {M i n' c a j g r e2 r'} : X.fbOK i a.fact j = true →
      r ∈ (applySummary a j g).facts → e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      JoinS [.sub M i n' c a] (.pub c.callee j g) (.base (.edge M i n' (limitF X.counted X.FL r')))

/-- Run 1 with the static rule as a pipeline system. -/
def sysDS : Sys PS MethodId MethodId where
  owner := PObj.owner sobjOwner
  roots := X.roots.map (fun M => .base (.init M zeroFact))
  rule  := RuleS X
  isSub := PObj.isSub
  isPub := PObj.isPub
  topic := PObj.topic sobjOwner
  join  := JoinS X

/-- The invariant of `sysDS`. -/
def InvS : PS → Prop
  | .base o => DS X o
  | .link m a M ic => LinkOK X.P (fun M i n f => DS X (.edge M i n f)) m a M ic
  | .sub M i n' c a => SubOK X.P (fun M i n f => DS X (.edge M i n f)) M i n' c a
  | .pub m j g => DS X (.init m j) ∧ DS X (.edge m j (X.P.exit m) g)
  | .zsub _ _ _ => False
  | .zpub _ _ => False

variable {X}

/-- `sysDS` is well formed. -/
theorem sysDS_wf : (sysDS X).WF where
  rule_ne := by
    intro ps c h
    cases h <;> exact List.cons_ne_nil _ _
  rule_local := by
    intro ps c h
    cases h with
    | pub => exact local_two _ rfl
    | answer => exact local_two _ rfl
    | sanswer => exact local_two _ rfl
    | reqUp => exact local_two _ rfl
    | sreqUp => exact local_two _ rfl
    | start => exact local_one _
    | step => exact local_one _
    | reqStmt => exact local_one _
    | sreqStmt => exact local_one _
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
  join_ne := by
    intro ss p c h
    cases h <;> exact List.cons_ne_nil _ _
  join_sub := by
    intro ss p c h
    cases h <;>
    · intro s hs
      rw [mem_one hs]
      exact ⟨rfl, rfl⟩
  join_pub := by
    intro ss p c h
    cases h <;> rfl
  join_owner := by
    intro ss p c h
    cases h <;> exact local_one _

theorem inv_of_clDS {x : PS} (h : Cl (sysDS X) x) : InvS X x := by
  induction h with
  | root hx =>
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hx
    exact DS.root hM
  | rule hr _ ih =>
    cases hr with
    | start => exact DS.start (fst_of ih :)
    | step he hf => exact DS.step (fst_of ih :) he hf
    | reqStmt he ht => exact DS.reqStmt (fst_of ih :) he ht
    | sreqStmt he hes hfire => exact DS.sreqStmt (fst_of ih :) he hes hfire
    | pass he hm => exact DS.pass (fst_of ih :) he hm
    | link he he1 ha => exact ⟨_, _, _, _, _, _, (fst_of ih :), he, rfl, he1, ha, rfl⟩
    | added =>
      obtain ⟨_, _, _, _, _, _, hf, he, rfl, he1, ha, rfl⟩ := (fst_of ih :)
      exact DS.added hf he he1 ha
    | initA => exact DS.initA (fst_of ih :)
    | sub he he1 ha => exact ⟨_, _, _, (fst_of ih :), he, he1, ha⟩
    | pub => exact ⟨(fst_of ih :), (snd_of ih :)⟩
    | reqSink hs hc => exact DS.reqSink (fst_of ih :) hs hc
    | answer hm hov => exact DS.answer (fst_of ih :) (snd_of ih :) hm hov
    | sanswer hok => exact DS.sanswer (fst_of ih :) (snd_of ih :) hok
    | reqUp hcl hov =>
      obtain ⟨_, _, _, _, _, _, hf, he, hc, he1, ha, rfl⟩ := (snd_of ih :)
      exact DS.reqUp (fst_of ih :) hf he hc he1 ha hcl hov
    | sreqUp hcl =>
      obtain ⟨_, _, _, _, _, _, hf, he, hc, he1, ha, rfl⟩ := (snd_of ih :)
      exact DS.sreqUp (fst_of ih :) hf he hc he1 ha hcl
    | vuln hs hc => exact DS.vuln (fst_of ih :) hs hc
    | clean he hf => exact DS.clean (fst_of ih :) he hf
    | reqClean he ht => exact DS.reqClean (fst_of ih :) he ht
    | filt he hp => exact DS.filt (fst_of ih :) he hp
  | join hj _ _ ihs ihp =>
    cases hj with
    | ret hap hr he2 hr' =>
      obtain ⟨_, _, _, hf, he, he1, ha⟩ := (fst_of ihs :)
      exact DS.ret hf he he1 ha ihp.1 hap ihp.2 hr he2 hr'
    | sret hok hr he2 hr' =>
      obtain ⟨_, _, _, hf, he, he1, ha⟩ := (fst_of ihs :)
      exact DS.sret hf he he1 ha ihp.1 hok ihp.2 hr he2 hr'

theorem cl_of_DS {o : SObj} (h : DS X o) : Cl (sysDS X) (.base o) := by
  induction h with
  | root hM => exact Cl.root (List.mem_map.2 ⟨_, hM, rfl⟩)
  | start _ ih => exact Cl.rule RuleS.start (all_one ih)
  | step _ he hf ih => exact Cl.rule (RuleS.step he hf) (all_one ih)
  | reqStmt _ he ht ih => exact Cl.rule (RuleS.reqStmt he ht) (all_one ih)
  | sreqStmt _ he hes hfire ih => exact Cl.rule (RuleS.sreqStmt he hes hfire) (all_one ih)
  | pass _ he hm ih => exact Cl.rule (RuleS.pass he hm) (all_one ih)
  | added _ he he1 ha ih =>
    exact Cl.rule RuleS.added (all_one (Cl.rule (RuleS.link he he1 ha) (all_one ih)))
  | initA _ ih => exact Cl.rule RuleS.initA (all_one ih)
  | ret _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    exact Cl.join (JoinS.ret hap hr he2 hr') (all_one (Cl.rule (RuleS.sub he he1 ha) (all_one ihf)))
      (Cl.rule RuleS.pub (all_two ihj ihg))
  | sret _ he he1 ha _ hok _ hr he2 hr' ihf ihj ihg =>
    exact Cl.join (JoinS.sret hok hr he2 hr')
      (all_one (Cl.rule (RuleS.sub he he1 ha) (all_one ihf)))
      (Cl.rule RuleS.pub (all_two ihj ihg))
  | reqSink _ hs hc ih => exact Cl.rule (RuleS.reqSink hs hc) (all_one ih)
  | answer _ _ hm hov ihr iha => exact Cl.rule (RuleS.answer hm hov) (all_two ihr iha)
  | sanswer _ _ hok ihs iha => exact Cl.rule (RuleS.sanswer hok) (all_two ihs iha)
  | reqUp _ _ he hc he1 ha hcl hov ihr ihf =>
    subst hc
    exact Cl.rule (RuleS.reqUp hcl hov)
      (all_two ihr (Cl.rule (RuleS.link he he1 ha) (all_one ihf)))
  | sreqUp _ _ he hc he1 ha hcl ihs ihf =>
    subst hc
    exact Cl.rule (RuleS.sreqUp hcl)
      (all_two ihs (Cl.rule (RuleS.link he he1 ha) (all_one ihf)))
  | vuln _ hs hc ih => exact Cl.rule (RuleS.vuln hs hc) (all_one ih)
  | clean _ he hf ih => exact Cl.rule (RuleS.clean he hf) (all_one ih)
  | reqClean _ he ht ih => exact Cl.rule (RuleS.reqClean he ht) (all_one ih)
  | filt _ he hp ih => exact Cl.rule (RuleS.filt he hp) (all_one ih)

/-- THE THEOREM for run 1 with the static rule: the pipeline closure on the closure objects is
    exactly `DS` (every variant of `SCtx`). -/
theorem clDS_iff {o : SObj} : Cl (sysDS X) (.base o) ↔ DS X o :=
  ⟨fun h => inv_of_clDS h, cl_of_DS⟩

theorem clDS_link {m : MethodId} {a : PFact} {M : MethodId} {ic : PFact} :
    Cl (sysDS X) (.link m a M ic) ↔ LinkOK X.P (fun M i n f => DS X (.edge M i n f)) m a M ic := by
  refine ⟨fun h => inv_of_clDS h, ?_⟩
  rintro ⟨_, _, _, _, _, _, hf, he, rfl, he1, ha, rfl⟩
  exact Cl.rule (RuleS.link he he1 ha) (all_one (cl_of_DS hf))

theorem clDS_sub {M : MethodId} {i : PFact} {n' : Node} {c : Call} {a : AFact} :
    Cl (sysDS X) (.sub M i n' c a) ↔ SubOK X.P (fun M i n f => DS X (.edge M i n f)) M i n' c a := by
  refine ⟨fun h => inv_of_clDS h, ?_⟩
  rintro ⟨_, _, _, hf, he, he1, ha⟩
  exact Cl.rule (RuleS.sub he he1 ha) (all_one (cl_of_DS hf))

theorem clDS_pub {m : MethodId} {j : PFact} {g : AFact} :
    Cl (sysDS X) (.pub m j g) ↔ DS X (.init m j) ∧ DS X (.edge m j (X.P.exit m) g) := by
  refine ⟨fun h => inv_of_clDS h, ?_⟩
  rintro ⟨hj, hg⟩
  exact Cl.rule RuleS.pub (all_two (cl_of_DS hj) (cl_of_DS hg))

theorem clDS_zsub {M : MethodId} {n' : Node} {c : Call} : ¬ Cl (sysDS X) (.zsub M n' c) :=
  fun h => inv_of_clDS h

theorem clDS_zpub {m : MethodId} {g : AFact} : ¬ Cl (sysDS X) (.zpub m g) :=
  fun h => inv_of_clDS h

end SysDS

/-! ## 7. The ND extension: the closure `ND.DN`

Edges carry PREMISE LISTS, so the links and subscriptions carry the premise list of the caller
edge, and a subscription names its CALL STATEMENT `(M, n, c, n')` (the partial matches of `DN`
are per call statement). A single-premise summary goes through `sub`/`pub` and the join `ret`
as in `D`. A summary with several premises is published as `ndpub m Pc g` and applied by ONE
k-ary JOIN with one subscription per premise, all at one call statement (spec §5.4; the
k-ary `join` of `Pipeline.Sys`): the list of subscriptions is aligned with `Pc` by `Combo`, in
the order in which `DN.ndBind` consumes the premises, and the join gives what `DN.ndRet` gives
after `DN.ndOpen` and one `DN.ndBind` per premise. The standing partial match `npart` is the
state of that join inside the caller (the conjunction store), not a pipeline object; every
other object of `DN` is exact (`clDN_iff`). -/

section SysDN
open ApSpec.ND

deriving instance DecidableEq for NObj

/-- The pipeline objects of `DN`. -/
inductive NPObj where
  | base  (o : NObj)
  /-- the callee `m` holds the link: added fact `a`, from a caller edge of `M` with premises `Pc` -/
  | link  (m : MethodId) (a : PFact) (M : MethodId) (Pc : List PFact)
  /-- the caller's subscription: a caller edge of `M` with premises `Pc` at the call statement
      `(M, n, c, n')` binds the fact `a` into the callee -/
  | sub   (M : MethodId) (Pc : List PFact) (n n' : Node) (c : Call) (a : AFact)
  /-- a published single-premise summary edge `j → g` of `m` -/
  | pub   (m : MethodId) (j : PFact) (g : AFact)
  /-- a published summary edge `Pc → g` of `m` with several premises -/
  | ndpub (m : MethodId) (Pc : List PFact) (g : AFact)
deriving DecidableEq

/-- The method of an object of `DN` (a partial match belongs to the caller). -/
def nobjOwner : NObj → MethodId
  | .ninit M _ => M
  | .nedge M _ _ _ => M
  | .nadded M _ => M
  | .nreq M _ _ => M
  | .nvuln M _ _ _ => M
  | .npart M _ _ _ _ _ _ => M

def NPObj.owner : NPObj → MethodId
  | .base o => nobjOwner o
  | .link m _ _ _ => m
  | .sub M _ _ _ _ _ => M
  | .pub m _ _ => m
  | .ndpub m _ _ => m

def NPObj.isSub : NPObj → Bool
  | .sub .. => true
  | _ => false

def NPObj.isPub : NPObj → Bool
  | .pub .. => true
  | .ndpub .. => true
  | _ => false

def NPObj.topic : NPObj → MethodId
  | .base o => nobjOwner o
  | .link m _ _ _ => m
  | .sub _ _ _ _ c _ => c.callee
  | .pub m _ _ => m
  | .ndpub m _ _ => m

/-- A full combination for a summary with several premises at the call statement
    `(M, n, c, n')`: the premises `cs` matched, in order, by the subscriptions `ss`; `P` is the
    concatenation of their premise lists and `d` the join of the layers of their bound facts
    (as `DN.ndBind` accumulates them). -/
inductive Combo (M : MethodId) (n n' : Node) (c : Call) :
    List PFact → List NPObj → List PFact → Bool → Prop where
  | nil : Combo M n n' c [] [] [] false
  | snoc {cs ss P d p Pf a} : Combo M n n' c cs ss P d → applicable p a.fact = true →
      Combo M n n' c (cs ++ [p]) (ss ++ [.sub M Pf n n' c a]) (P ++ Pf) (d || a.demand)

variable (X : Ctx)

/-- The local rules of `DN` (the partial match is inside the join `nd`). -/
inductive RuleN : List NPObj → NPObj → Prop where
  | start {M i} :
      RuleN [.base (.ninit M i)] (.base (.nedge M [i] (X.Q.prog.entry M) (startFact i)))
  | step {M P n f n' s f'} : (M, n, Instr.stmt s, n') ∈ X.Q.prog.edges →
      f' ∈ (transfer X.counted X.FL s f).facts →
      RuleN [.base (.nedge M P n f)] (.base (.nedge M P n' f'))
  | reqStmt {M i n f n' s t} : (M, n, Instr.stmt s, n') ∈ X.Q.prog.edges →
      t ∈ (transfer X.counted X.FL s f).reqs →
      RuleN [.base (.nedge M [i] n f)] (.base (.nreq M i t))
  | pass {M P n f n' c} : (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      memB f.fact.base c.touched = false →
      RuleN [.base (.nedge M P n f)] (.base (.nedge M P n' f))
  | link {M P n f n' c e a} : (M, n, Instr.call c, n') ∈ X.Q.prog.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts →
      RuleN [.base (.nedge M P n f)] (.link c.callee a.fact M P)
  | added {m a M P} : RuleN [.link m a M P] (.base (.nadded m a))
  | initA {m a} : RuleN [.base (.nadded m a)] (.base (.ninit m (X.α m a)))
  | sub {M P n f n' c e a} : (M, n, Instr.call c, n') ∈ X.Q.prog.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts →
      RuleN [.base (.nedge M P n f)] (.sub M P n n' c a)
  | pub {m j g} :
      RuleN [.base (.ninit m j), .base (.nedge m [j] (X.Q.prog.exit m) g)] (.pub m j g)
  | ndpub {m Pc g} : 2 ≤ Pc.length →
      RuleN [.base (.nedge m Pc (X.Q.prog.exit m) g)] (.ndpub m Pc g)
  | reqSink {M i n f s t} : (M, n, s) ∈ X.sinks → check i f s = .request t →
      RuleN [.base (.nedge M [i] n f)] (.base (.nreq M i t))
  | answer {M i t a} : a.mark = .conc t → overlapB a i = true →
      RuleN [.base (.nreq M i t), .base (.nadded M a)] (.base (.ninit M (answerInit i a t)))
  | reqUp {m j t a M ic} : climbsB a.mark t = true → overlapB a j = true →
      RuleN [.base (.nreq m j t), .link m a M [ic]] (.base (.nreq M ic t))
  | vuln {M P n f s i} : (M, n, s) ∈ X.sinks → i ∈ P → check i f s = .triggered →
      RuleN [.base (.nedge M P n f)] (.base (.nvuln M n s f.demand))
  | clean {M P n f n' cl f'} : (M, n, Instr.clean cl, n') ∈ X.Q.prog.edges →
      f' ∈ (cleanRes cl f).facts →
      RuleN [.base (.nedge M P n f)] (.base (.nedge M P n' f'))
  | reqClean {M i n f n' cl t} : (M, n, Instr.clean cl, n') ∈ X.Q.prog.edges →
      t ∈ (cleanRes cl f).reqs →
      RuleN [.base (.nedge M [i] n f)] (.base (.nreq M i t))
  | filt {M P n f n' b may} : (M, n, Instr.filt b may, n') ∈ X.Q.prog.edges →
      (f.fact.base = b → may f.fact.path = true) →
      RuleN [.base (.nedge M P n f)] (.base (.nedge M P n' f))
  | conj {M P1 n f1 P2 f2 cj n'} : (M, n, cj, n') ∈ X.Q.conjs →
      overlapB f1.fact cj.lit1 = true → markGate cj.lit1.mark f1.fact.mark = .ok →
      overlapB f2.fact cj.lit2 = true → markGate cj.lit2.mark f2.fact.mark = .ok →
      RuleN [.base (.nedge M P1 n f1), .base (.nedge M P2 n f2)]
        (.base (.nedge M (P1 ++ P2) n' (conjFact cj f1 f2)))
  | reqConj {M i n f cj n' lit t} : (M, n, cj, n') ∈ X.Q.conjs → (lit = cj.lit1 ∨ lit = cj.lit2) →
      overlapB f.fact lit = true → markGate lit.mark f.fact.mark = .req t →
      RuleN [.base (.nedge M [i] n f)] (.base (.nreq M i t))

/-- The joins of `DN`: the single-premise `ret`, and the k-ary `nd` (one subscription per
    premise of a summary with several premises, all at one call statement). -/
inductive JoinN : List NPObj → NPObj → NPObj → Prop where
  | ret {M P n n' c a j g r e2 r'} : applicable j a.fact = true →
      r ∈ (applySummary a j g).facts → e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      JoinN [.sub M P n n' c a] (.pub c.callee j g)
        (.base (.nedge M P n' (limitF X.counted X.FL r')))
  | nd {M n n' c Pc ss P d g e2 r} : Combo M n n' c Pc ss P d → 2 ≤ Pc.length →
      e2 ∈ c.fromCallee → r ∈ (applyEdge ⟨g.fact, g.demand || d⟩ e2.1 e2.2).facts →
      JoinN ss (.ndpub c.callee Pc g) (.base (.nedge M P n' (limitF X.counted X.FL r)))

/-- The ND run as a pipeline system. -/
def sysDN : Sys NPObj MethodId MethodId where
  owner := NPObj.owner
  roots := X.roots.map (fun M => .base (.ninit M zeroFact))
  rule  := RuleN X
  isSub := NPObj.isSub
  isPub := NPObj.isPub
  topic := NPObj.topic
  join  := JoinN X

/-- The objects of `DN` that are pipeline objects: all but the partial matches. -/
def NoPart : NObj → Prop
  | .npart .. => False
  | _ => True

/-- What a subscription of `DN` means. -/
def NSubOK (M : MethodId) (Pc : List PFact) (n n' : Node) (c : Call) (a : AFact) : Prop :=
  ∃ (f : AFact) (e : MicroEdge), DN X (.nedge M Pc n f) ∧
    (M, n, Instr.call c, n') ∈ X.Q.prog.edges ∧ e ∈ c.toCallee ∧ a ∈ (applyEdge f e.1 e.2).facts

/-- The invariant of `sysDN`. -/
def InvN : NPObj → Prop
  | .base o => DN X o ∧ NoPart o
  | .link m a M Pc => LinkOK X.Q.prog (fun M P n f => DN X (.nedge M P n f)) m a M Pc
  | .sub M Pc n n' c a => NSubOK X M Pc n n' c a
  | .pub m j g => DN X (.ninit m j) ∧ DN X (.nedge m [j] (X.Q.prog.exit m) g)
  | .ndpub m Pc g => DN X (.nedge m Pc (X.Q.prog.exit m) g) ∧ 2 ≤ Pc.length

/-- The induction motive of the completeness proof. A partial match `npart M n c n' rest P g` of
    `DN` is a partial combination: a publication `cs ++ rest → g0` in the pipeline closure and
    subscriptions in the pipeline closure that match `cs`. -/
def MotN : NObj → Prop
  | .npart M n c n' rest P g =>
    (M, n, Instr.call c, n') ∈ X.Q.prog.edges ∧
    ∃ (cs : List PFact) (g0 : AFact) (ss : List NPObj) (d : Bool),
      Cl (sysDN X) (.ndpub c.callee (cs ++ rest) g0) ∧ 2 ≤ (cs ++ rest).length ∧
      (∀ s ∈ ss, Cl (sysDN X) s) ∧ Combo M n n' c cs ss P d ∧ g = ⟨g0.fact, g0.demand || d⟩
  | o => Cl (sysDN X) (.base o)

variable {X}

/-! ### Combinations -/

theorem combo_subs {M : MethodId} {n n' : Node} {c : Call} {cs : List PFact} {ss : List NPObj}
    {P : List PFact} {d : Bool} (h : Combo M n n' c cs ss P d) :
    ∀ s ∈ ss, ∃ (Pf : List PFact) (a : AFact), s = .sub M Pf n n' c a := by
  induction h with
  | nil => intro s hs; cases hs
  | snoc _ _ ih =>
    intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · exact ih s hs
    · exact ⟨_, _, mem_one hs⟩

theorem combo_ne {M : MethodId} {n n' : Node} {c : Call} {cs : List PFact} {ss : List NPObj}
    {P : List PFact} {d : Bool} (h : Combo M n n' c cs ss P d) (hlen : 2 ≤ cs.length) :
    ss ≠ [] := by
  cases h with
  | nil => exact absurd hlen (by decide)
  | snoc =>
    intro he
    have := congrArg List.length he
    simp at this

/-- A combination with at least one premise has its call statement in the program. -/
theorem combo_edge {M : MethodId} {n n' : Node} {c : Call} {cs : List PFact} {ss : List NPObj}
    {P : List PFact} {d : Bool} (h : Combo M n n' c cs ss P d) (hlen : 2 ≤ cs.length)
    (hss : ∀ s ∈ ss, InvN X s) : (M, n, Instr.call c, n') ∈ X.Q.prog.edges := by
  cases h with
  | nil => exact absurd hlen (by decide)
  | snoc =>
    obtain ⟨_, _, _, he, _, _⟩ := (hss _ (List.mem_append_right _ List.mem_cons_self) :)
    exact he

/-- A combination is a chain of `DN.ndBind`: from the opened match of `cs ++ rest`, `DN` reaches
    the match of `rest` with the premise list and the layer of the combination. -/
theorem combo_chain {M : MethodId} {n n' : Node} {c : Call} {cs : List PFact} {ss : List NPObj}
    {P : List PFact} {d : Bool} (h : Combo M n n' c cs ss P d) (hss : ∀ s ∈ ss, InvN X s)
    (g : AFact) : ∀ rest, DN X (.npart M n c n' (cs ++ rest) [] g) →
      DN X (.npart M n c n' rest P ⟨g.fact, g.demand || d⟩) := by
  induction h with
  | nil =>
    intro rest h0
    rw [Bool.or_false]
    exact h0
  | @snoc cs ss P d p Pf a _ hap ih =>
    intro rest h0
    have ih' := ih (fun s hs => hss s (List.mem_append_left _ hs)) (p :: rest)
      (by rw [List.append_assoc] at h0; exact h0)
    obtain ⟨_, _, hf, _, he1, ha⟩ := (hss _ (List.mem_append_right _ List.mem_cons_self) :)
    have h1 := DN.ndBind ih' hf he1 ha hap
    rw [Bool.or_assoc] at h1
    exact h1

theorem combo_snoc_mem {ss : List NPObj} {x s : NPObj} (h : s ∈ ss ++ [x]) : s ∈ ss ∨ s = x := by
  rcases List.mem_append.1 h with h | h
  · exact .inl h
  · exact .inr (mem_one h)

/-! ### Well-formedness, soundness, completeness -/

/-- `sysDN` is well formed. -/
theorem sysDN_wf : (sysDN X).WF where
  rule_ne := by
    intro ps c h
    cases h <;> exact List.cons_ne_nil _ _
  rule_local := by
    intro ps c h
    cases h with
    | pub => exact local_two _ rfl
    | answer => exact local_two _ rfl
    | reqUp => exact local_two _ rfl
    | conj => exact local_two _ rfl
    | start => exact local_one _
    | step => exact local_one _
    | reqStmt => exact local_one _
    | pass => exact local_one _
    | link => exact local_one _
    | added => exact local_one _
    | initA => exact local_one _
    | sub => exact local_one _
    | ndpub => exact local_one _
    | reqSink => exact local_one _
    | vuln => exact local_one _
    | clean => exact local_one _
    | reqClean => exact local_one _
    | filt => exact local_one _
    | reqConj => exact local_one _
  join_ne := by
    intro ss p c h
    cases h with
    | ret => exact List.cons_ne_nil _ _
    | nd hc hlen => exact combo_ne hc hlen
  join_sub := by
    intro ss p c h
    cases h with
    | ret =>
      intro s hs
      rw [mem_one hs]
      exact ⟨rfl, rfl⟩
    | nd hc =>
      intro s hs
      obtain ⟨_, _, rfl⟩ := combo_subs hc s hs
      exact ⟨rfl, rfl⟩
  join_pub := by
    intro ss p c h
    cases h <;> rfl
  join_owner := by
    intro ss p c h
    cases h with
    | ret => exact local_one _
    | nd hc =>
      intro s hs s' hs'
      obtain ⟨_, _, rfl⟩ := combo_subs hc s hs
      obtain ⟨_, _, rfl⟩ := combo_subs hc s' hs'
      rfl

theorem inv_of_clDN {x : NPObj} (h : Cl (sysDN X) x) : InvN X x := by
  induction h with
  | root hx =>
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hx
    exact ⟨DN.root hM, trivial⟩
  | rule hr _ ih =>
    cases hr with
    | start => exact ⟨DN.start (fst_of ih :).1, trivial⟩
    | step he hf => exact ⟨DN.step (fst_of ih :).1 he hf, trivial⟩
    | reqStmt he ht => exact ⟨DN.reqStmt (fst_of ih :).1 he ht, trivial⟩
    | pass he hm => exact ⟨DN.pass (fst_of ih :).1 he hm, trivial⟩
    | link he he1 ha => exact ⟨_, _, _, _, _, _, (fst_of ih :).1, he, rfl, he1, ha, rfl⟩
    | added =>
      obtain ⟨_, _, _, _, _, _, hf, he, rfl, he1, ha, rfl⟩ := (fst_of ih :)
      exact ⟨DN.added hf he he1 ha, trivial⟩
    | initA => exact ⟨DN.initA (fst_of ih :).1, trivial⟩
    | sub he he1 ha => exact ⟨_, _, (fst_of ih :).1, he, he1, ha⟩
    | pub => exact ⟨(fst_of ih :).1, (snd_of ih :).1⟩
    | ndpub hlen => exact ⟨(fst_of ih :).1, hlen⟩
    | reqSink hs hc => exact ⟨DN.reqSink (fst_of ih :).1 hs hc, trivial⟩
    | answer hm hov => exact ⟨DN.answer (fst_of ih :).1 (snd_of ih :).1 hm hov, trivial⟩
    | reqUp hcl hov =>
      obtain ⟨_, _, _, _, _, _, hf, he, hc, he1, ha, rfl⟩ := (snd_of ih :)
      exact ⟨DN.reqUp (fst_of ih :).1 hf he hc he1 ha hcl hov, trivial⟩
    | vuln hs hi hc => exact ⟨DN.vuln (fst_of ih :).1 hs hi hc, trivial⟩
    | clean he hf => exact ⟨DN.clean (fst_of ih :).1 he hf, trivial⟩
    | reqClean he ht => exact ⟨DN.reqClean (fst_of ih :).1 he ht, trivial⟩
    | filt he hp => exact ⟨DN.filt (fst_of ih :).1 he hp, trivial⟩
    | conj hcj ho1 hg1 ho2 hg2 =>
      exact ⟨DN.conj (fst_of ih :).1 (snd_of ih :).1 hcj ho1 hg1 ho2 hg2, trivial⟩
    | reqConj hcj hlit hov hg => exact ⟨DN.reqConj (fst_of ih :).1 hcj hlit hov hg, trivial⟩
  | join hj _ _ ihs ihp =>
    cases hj with
    | ret hap hr he2 hr' =>
      obtain ⟨_, _, hf, he, he1, ha⟩ := (fst_of ihs :)
      exact ⟨DN.ret hf he he1 ha ihp.1 hap ihp.2 hr he2 hr', trivial⟩
    | @nd M n n' c Pc ss P d g e2 r hc hlen he2 hr =>
      have h0 : DN X (.npart M n c n' (Pc ++ []) [] g) := by
        rw [List.append_nil]
        exact DN.ndOpen (combo_edge hc hlen ihs) ihp.1 hlen
      exact ⟨DN.ndRet (combo_chain hc ihs g [] h0) he2 hr, trivial⟩

theorem motN_of_DN {o : NObj} (h : DN X o) : MotN X o := by
  induction h with
  | root hM => exact Cl.root (List.mem_map.2 ⟨_, hM, rfl⟩)
  | start _ ih => exact Cl.rule RuleN.start (all_one ih)
  | step _ he hf ih => exact Cl.rule (RuleN.step he hf) (all_one ih)
  | reqStmt _ he ht ih => exact Cl.rule (RuleN.reqStmt he ht) (all_one ih)
  | pass _ he hm ih => exact Cl.rule (RuleN.pass he hm) (all_one ih)
  | added _ he he1 ha ih =>
    exact Cl.rule RuleN.added (all_one (Cl.rule (RuleN.link he he1 ha) (all_one ih)))
  | initA _ ih => exact Cl.rule RuleN.initA (all_one ih)
  | ret _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    exact Cl.join (JoinN.ret hap hr he2 hr')
      (all_one (Cl.rule (RuleN.sub he he1 ha) (all_one ihf)))
      (Cl.rule RuleN.pub (all_two ihj ihg))
  | @ndOpen M n c n' Pc g he _ hlen ihg =>
    refine ⟨he, [], g, [], false, ?_, hlen, ?_, Combo.nil, ?_⟩
    · exact Cl.rule (RuleN.ndpub hlen) (all_one ihg)
    · intro _ hs
      cases hs
    · rw [Bool.or_false]
  | @ndBind M n c n' p ps P g Pf f e1 a _ _ he1 ha hap ihp ihf =>
    obtain ⟨he, cs, g0, ss, d, hpub, hlen, hss, hc, rfl⟩ := ihp
    have hs : Cl (sysDN X) (.sub M Pf n n' c a) := Cl.rule (RuleN.sub he he1 ha) (all_one ihf)
    refine ⟨he, cs ++ [p], g0, ss ++ [.sub M Pf n n' c a], d || a.demand, ?_, ?_, ?_,
      Combo.snoc hc hap, ?_⟩
    · rw [List.append_assoc]; exact hpub
    · rw [List.append_assoc]; exact hlen
    · intro s hs'
      rcases combo_snoc_mem hs' with hs' | rfl
      · exact hss s hs'
      · exact hs
    · show (⟨g0.fact, (g0.demand || d) || a.demand⟩ : AFact) = ⟨g0.fact, g0.demand || (d || a.demand)⟩
      rw [Bool.or_assoc]
  | ndRet _ he2 hr ihp =>
    obtain ⟨_, cs, g0, ss, d, hpub, hlen, hss, hc, rfl⟩ := ihp
    rw [List.append_nil] at hpub hlen
    exact Cl.join (JoinN.nd hc hlen he2 hr) hss hpub
  | reqSink _ hs hc ih => exact Cl.rule (RuleN.reqSink hs hc) (all_one ih)
  | answer _ _ hm hov ihr iha => exact Cl.rule (RuleN.answer hm hov) (all_two ihr iha)
  | reqUp _ _ he hc he1 ha hcl hov ihr ihf =>
    subst hc
    exact Cl.rule (RuleN.reqUp hcl hov)
      (all_two ihr (Cl.rule (RuleN.link he he1 ha) (all_one ihf)))
  | vuln _ hs hi hc ih => exact Cl.rule (RuleN.vuln hs hi hc) (all_one ih)
  | clean _ he hf ih => exact Cl.rule (RuleN.clean he hf) (all_one ih)
  | reqClean _ he ht ih => exact Cl.rule (RuleN.reqClean he ht) (all_one ih)
  | filt _ he hp ih => exact Cl.rule (RuleN.filt he hp) (all_one ih)
  | conj _ _ hcj ho1 hg1 ho2 hg2 ih1 ih2 =>
    exact Cl.rule (RuleN.conj hcj ho1 hg1 ho2 hg2) (all_two ih1 ih2)
  | reqConj _ hcj hlit hov hg ih => exact Cl.rule (RuleN.reqConj hcj hlit hov hg) (all_one ih)

theorem cl_of_DN {o : NObj} (h : DN X o) (hn : NoPart o) : Cl (sysDN X) (.base o) := by
  have hm := motN_of_DN h
  cases o with
  | npart => exact hn.elim
  | ninit => exact hm
  | nedge => exact hm
  | nadded => exact hm
  | nreq => exact hm
  | nvuln => exact hm

/-- THE THEOREM for the ND run: the pipeline closure on the closure objects is exactly `DN`
    without the partial matches (which are the state of the k-ary join, not pipeline objects). -/
theorem clDN_iff {o : NObj} : Cl (sysDN X) (.base o) ↔ DN X o ∧ NoPart o :=
  ⟨fun h => inv_of_clDN h, fun ⟨h, hn⟩ => cl_of_DN h hn⟩

theorem clDN_nedge {M : MethodId} {P : List PFact} {n : Node} {f : AFact} :
    Cl (sysDN X) (.base (.nedge M P n f)) ↔ DN X (.nedge M P n f) :=
  ⟨fun h => (clDN_iff.1 h).1, fun h => clDN_iff.2 ⟨h, trivial⟩⟩

theorem clDN_ninit {M : MethodId} {i : PFact} :
    Cl (sysDN X) (.base (.ninit M i)) ↔ DN X (.ninit M i) :=
  ⟨fun h => (clDN_iff.1 h).1, fun h => clDN_iff.2 ⟨h, trivial⟩⟩

theorem clDN_nadded {M : MethodId} {a : PFact} :
    Cl (sysDN X) (.base (.nadded M a)) ↔ DN X (.nadded M a) :=
  ⟨fun h => (clDN_iff.1 h).1, fun h => clDN_iff.2 ⟨h, trivial⟩⟩

theorem clDN_nreq {M : MethodId} {i : PFact} {t : Mark} :
    Cl (sysDN X) (.base (.nreq M i t)) ↔ DN X (.nreq M i t) :=
  ⟨fun h => (clDN_iff.1 h).1, fun h => clDN_iff.2 ⟨h, trivial⟩⟩

theorem clDN_nvuln {M : MethodId} {n : Node} {s : PFact} {d : Bool} :
    Cl (sysDN X) (.base (.nvuln M n s d)) ↔ DN X (.nvuln M n s d) :=
  ⟨fun h => (clDN_iff.1 h).1, fun h => clDN_iff.2 ⟨h, trivial⟩⟩

theorem clDN_npart {M : MethodId} {n : Node} {c : Call} {n' : Node} {rest P : List PFact}
    {g : AFact} : ¬ Cl (sysDN X) (.base (.npart M n c n' rest P g)) :=
  fun h => (clDN_iff.1 h).2

theorem clDN_link {m : MethodId} {a : PFact} {M : MethodId} {Pc : List PFact} :
    Cl (sysDN X) (.link m a M Pc) ↔
      LinkOK X.Q.prog (fun M P n f => DN X (.nedge M P n f)) m a M Pc := by
  refine ⟨fun h => inv_of_clDN h, ?_⟩
  rintro ⟨_, _, _, _, _, _, hf, he, rfl, he1, ha, rfl⟩
  exact Cl.rule (RuleN.link he he1 ha) (all_one (clDN_nedge.2 hf))

theorem clDN_sub {M : MethodId} {Pc : List PFact} {n n' : Node} {c : Call} {a : AFact} :
    Cl (sysDN X) (.sub M Pc n n' c a) ↔ NSubOK X M Pc n n' c a := by
  refine ⟨fun h => inv_of_clDN h, ?_⟩
  rintro ⟨_, _, hf, he, he1, ha⟩
  exact Cl.rule (RuleN.sub he he1 ha) (all_one (clDN_nedge.2 hf))

theorem clDN_pub {m : MethodId} {j : PFact} {g : AFact} :
    Cl (sysDN X) (.pub m j g) ↔ DN X (.ninit m j) ∧ DN X (.nedge m [j] (X.Q.prog.exit m) g) := by
  refine ⟨fun h => inv_of_clDN h, ?_⟩
  rintro ⟨hj, hg⟩
  exact Cl.rule RuleN.pub (all_two (clDN_ninit.2 hj) (clDN_nedge.2 hg))

theorem clDN_ndpub {m : MethodId} {Pc : List PFact} {g : AFact} :
    Cl (sysDN X) (.ndpub m Pc g) ↔ DN X (.nedge m Pc (X.Q.prog.exit m) g) ∧ 2 ≤ Pc.length := by
  refine ⟨fun h => inv_of_clDN h, ?_⟩
  rintro ⟨hg, hlen⟩
  exact Cl.rule (RuleN.ndpub hlen) (all_one (clDN_nedge.2 hg))

end SysDN

/-! ## 8. Axiom audit -/

#print axioms sysD_wf
#print axioms clD_iff
#print axioms clD_link
#print axioms clD_sub
#print axioms clD_pub
#print axioms clD_zsub
#print axioms clD_zpub
#print axioms sysDR_wf
#print axioms clDR_iff
#print axioms clDR_link
#print axioms clDR_sub
#print axioms clDR_pub
#print axioms clDR_zsub
#print axioms clDR_zpub
#print axioms sysDB_wf
#print axioms clDB_iff
#print axioms clDB_link
#print axioms clDB_sub
#print axioms clDB_pub
#print axioms clDB_zsub
#print axioms clDB_zpub
#print axioms sysDS_wf
#print axioms clDS_iff
#print axioms clDS_link
#print axioms clDS_sub
#print axioms clDS_pub
#print axioms clDS_zsub
#print axioms clDS_zpub
#print axioms sysDN_wf
#print axioms clDN_iff
#print axioms clDN_nedge
#print axioms clDN_ninit
#print axioms clDN_nadded
#print axioms clDN_nreq
#print axioms clDN_nvuln
#print axioms clDN_link
#print axioms clDN_sub
#print axioms clDN_pub
#print axioms clDN_npart
#print axioms clDN_ndpub

end ApSpec.PipelineAP
