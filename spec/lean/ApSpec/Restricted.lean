/-
  ApSpec.Restricted — runs that strictly follow the demand of the previous run.

  Run 1 is the closure `D` of `Basic.lean` with the abstraction `policy1` (the most
  abstract fact; no demand). Every later run is the closure `DR` below:
    * the abstraction emits an initial fact only through the emission table `emit`
      (spec §6.3), from a demand edge of the callee;
    * a callee summary edge is applied only after the restriction `restrict` by a demand
      edge of the callee (spec §6.4);
    * the caller applies a summary when its fact SATISFIES the premise (`sat`, spec §4.3);
    * persisted complete records (`recs`) of earlier runs are applied as they are, and can
      ALWAYS be reused (the user's decision): a record applies when the caller fact satisfies
      its premise (`sat`) OR when its premise covers the caller fact (`applicable`, the run-1
      direction). With `satI` alone, a run-1 record with the premise `(arg0, [], *, {}, *)`
      would never apply to a concrete caller fact such as `(arg0, [f], $, T)`.

  The demand edges come from the previous run (in the other direction). They are
  given here in FORWARD orientation: `din` is the entry pattern (D-c, the conclusion of
  the backward demand edge) and `dout` is the exit pattern (D-p, its premise), or `none`
  when the demand does not reach the exit (the sink is in the method or below it).
  The restriction compares LOCATIONS only (marks are ignored); the emission `emitM` and the
  entry coverage of `FlowR`/`ReachR` also compare the mark.

  The rules of the spec (versions 4 and 5):
    * `emitM` (§1b): the MARK-AWARE emission. A demand entry pattern with the concrete mark `T`
      asks for `T`: an added fact with the mark `T` emits its matching part (`a ∩ D-c`); another
      mark gives nothing. No request is necessary: a restricted run starts from the zero fact and
      `emitM` copies the mark of the added fact, so every added fact has a concrete mark. The contract is `EmitContractConc` (concrete added facts);
      the coverage proof uses it through `EmitContractOn` and the concreteness of the run;
    * `satI`: the caller applies a summary if the premise lies inside its fact and the premise
      mark admits the fact mark (`satO`, the overlap form, is also sound but admits reads of a
      coarser sibling premise);
    * `restrictU`: the restriction as agreed with the user.
  Version 3 rules, kept as the record of the review: the location-only tables `emitU` (as agreed)
  and `emitS` (the version-3 repair), `satU`/`satS`, `restrictS` (contract `EmitContract`, for
  every added fact). The contracts `EmitContractOn`, `SatContract`, `RestrictContract` are what
  the coverage proof needs.
-/
import ApSpec.Basic

namespace ApSpec

/-- The location set of a pattern, without marks. -/
def PFact.coversLoc (i : PFact) (l : Loc) : Prop :=
  l.base = i.base ∧ ∃ σ, l.path = i.path ++ σ ∧ tailI i.kind σ

/-- A demand edge of the previous run, in forward orientation. `dout = none`: the demand
    does not reach the method exit (only the entry is demanded). -/
structure DemandEdge where
  din  : PFact
  dout : Option PFact
deriving DecidableEq, Repr

/-- The run-1 abstraction: the most abstract fact (and the zero fact for itself). -/
def policy1 : MethodId → PFact → PFact := policy (fun _ => [])

/-- The most abstract initial fact on the demand chain. -/
def chainFact (d : PFact) (p : List Acc) : PFact := ⟨d.base, p, .star Excl.empty, .star⟩

/-! ## 1. The version-3 emission tables (the record of the review) -/

/-- The emission table as agreed in the review. `d` is the demand entry pattern (D-c),
    `a` the added fact. -/
def emitU (d a : PFact) : Option PFact :=
  if Nat.beq d.base a.base then
    match relate d.path a.path with
    | .below (g :: _) =>
      -- below the demand chain: one accessor more than the chain
      if admitsTailB d.kind [g] then some (chainFact d (d.path ++ [g])) else none
    | .below [] =>
      -- at the demand chain: the added fact's own tail
      match a.kind with
      | .exact  => some ⟨d.base, d.path, .exact, .star⟩
      | .any    => some ⟨d.base, d.path, .any, .star⟩
      | .star _ => some (chainFact d d.path)
    | .above _ =>
      match a.kind with
      | .any => some (chainFact d d.path)   -- the requested chain is in the [any]
      | _    => none                        -- U: a `*` fact above cannot satisfy it
    | .apart => none
  else none

/-- The sound emission table: as `emitU`, and a `*` added fact above the demand chain
    (whose exclusion admits the rest of the chain) emits the demand chain. -/
def emitS (d a : PFact) : Option PFact :=
  if Nat.beq d.base a.base then
    match relate d.path a.path with
    | .below (g :: _) =>
      if admitsTailB d.kind [g] then some (chainFact d (d.path ++ [g])) else none
    | .below [] =>
      match a.kind with
      | .exact  => some ⟨d.base, d.path, .exact, .star⟩
      | .any    => some ⟨d.base, d.path, .any, .star⟩
      | .star _ => some (chainFact d d.path)
    | .above r =>
      match a.kind with
      | .any    => some (chainFact d d.path)
      | .star e => if e.admits r then some (chainFact d d.path) else none
      | .exact  => none
    | .apart => none
  else none

/-! ## 1b. The mark-aware emission (spec §6.3) -/

/-- The meet of two premise tails at the same path: the continuations that both admit. -/
def meetK : Kind → Kind → Kind
  | .any, k => k
  | k, .any => k
  | .exact, _ => .exact
  | _, .exact => .exact
  | .star e1, .star e2 => .star (e1.union e2)

/-- The demand entry pattern `d` asks for the mark of `a`: a `*` demand mark admits every mark;
    a concrete demand mark `T` needs the concrete mark `T` (a `*` fact mark never meets it in a
    restricted run: every added fact there has a concrete mark). -/
def markMatchB : MarkA → MarkA → Bool
  | .star,     _         => true
  | .conc t,   .conc t'  => Nat.beq t t'
  | .conc _,   .star     => false
  | .conc _,   .starEx _ => false
  | .starEx _, _         => true     -- a demand pattern never has `starEx`

/-- The spec emission (since version 4): the part of the added fact `a` that the demand entry pattern `d`
    covers (`a ∩ D-c`), with the mark of `a`. -/
def emitM (d a : PFact) : Option PFact :=
  if Nat.beq d.base a.base && markMatchB d.mark a.mark then
    match relate d.path a.path with
    | .below [] => some ⟨a.base, a.path, meetK a.kind d.kind, a.mark⟩
    | .below r  => if admitsTailB d.kind r then some a else none
    | .above r  => if admitsTailB a.kind r then some ⟨d.base, d.path, d.kind, a.mark⟩ else none
    | .apart    => none
  else none

/-! ## 2. Satisfaction of a summary premise (spec §4.3) -/

/-- The added fact `a` is strictly above the premise `j`. -/
def aboveB (j a : PFact) : Bool :=
  match dropPrefix a.path j.path with
  | some (_ :: _) => true
  | _ => false

/-- As agreed: the caller fact `a` satisfies the premise `j` if `j` covers it
    (`applicable`), or if `a` is an `[any]` fact above `j` and the premise mark admits
    the fact mark. The application then takes the not-strong-enough case. -/
def satU (j a : PFact) : Bool :=
  applicable j a ||
  (Nat.beq j.base a.base && a.kind.isAny && markSubB j.mark a.mark && aboveB j a)

/-- The sound satisfaction: as `satU`, and also a `*` fact above `j` whose exclusion
    admits the rest of the premise chain. -/
def satS (j a : PFact) : Bool :=
  satU j a ||
  (Nat.beq j.base a.base && a.kind.isStar && markSubB j.mark a.mark &&
    (match dropPrefix a.path j.path with
     | some (x :: r) => admitsTailB a.kind (x :: r)
     | _ => false))

/-- The overlap satisfaction (version 4; sound, but not the spec rule): the premise overlaps the fact (a common location, marks
    ignored) and the premise mark admits the fact mark (so the mark gate never raises a request
    from a summary application). -/
def satO (j a : PFact) : Bool :=
  overlapB j a && markSubB j.mark a.mark

/-- The spec satisfaction (version 5): the premise lies INSIDE the fact (the fact
    covers every location of the premise) and the premise mark admits the fact mark. The emitted
    fact `a ∩ D-c` always lies inside its added fact, so this is enough; it rejects the reads of a
    coarser sibling premise that `satO` admits (review of version 4, M2). -/
def satI (j a : PFact) : Bool :=
  coversB ⟨a.base, a.path, a.kind, .star⟩ j && markSubB j.mark a.mark
-- (the location part of `a` covers `j`; the marks are compared only as the contract needs: a concrete fact
--  satisfies a `*`-premise record, and a cleaned fact `*∖x` satisfies a `*` premise — review of round 5)

/-! ## 3. Restriction of a summary edge by a demand edge (spec §6.4) -/

/-- The restricted conclusion as agreed: `R-c := concat(D-p, delta(S-c, D-p))`.
    A correlated `*` conclusion above `D-p` gives nothing. -/
def restrictConcU (sc : AFact) (dout : PFact) : Option AFact :=
  if Nat.beq sc.fact.base dout.base then
    match relate dout.path sc.fact.path with
    | .below r => if admitsTailB dout.kind r then some sc else none
    | .above _ =>
      match sc.fact.kind with
      | .any => some ⟨⟨sc.fact.base, dout.path,
                  (match dout.kind with | .exact => .exact | _ => .any), sc.fact.mark⟩, sc.demand⟩
      | _    => none
    | .apart => none
  else none

/-- The sound restricted conclusion: as `restrictConcU`, but a correlated `*` conclusion
    above `D-p` keeps the edge as it is. The exact restriction would move the premise
    down, and that loses the correlation; the edge keeps more pairs but adds no demand. -/
def restrictConcS (sc : AFact) (dout : PFact) : Option AFact :=
  if Nat.beq sc.fact.base dout.base then
    match relate dout.path sc.fact.path with
    | .below r => if admitsTailB dout.kind r then some sc else none
    | .above r =>
      match sc.fact.kind with
      | .star e => if e.admits r then some sc else none
      | .any    => some ⟨⟨sc.fact.base, dout.path,
                      (match dout.kind with | .exact => .exact | _ => .any), sc.fact.mark⟩, sc.demand⟩
      | .exact  => none
    | .apart => none
  else none

/-- The restriction of the summary edge `sp → sc` by the demand edge `d`, for a given
    conclusion restriction: `R-p := S-p` if `S-p` overlaps `D-c`, else nothing (`S-p` is
    one path, so the intersection is all of it or nothing). No `D-p`: no summary. -/
def restrictWith (rc : AFact → PFact → Option AFact) (sp : PFact) (sc : AFact) (d : DemandEdge) :
    Option AFact :=
  match d.dout with
  | none => none
  | some p => if overlapB sp d.din then rc sc p else none

def restrictU : PFact → AFact → DemandEdge → Option AFact := restrictWith restrictConcU
def restrictS : PFact → AFact → DemandEdge → Option AFact := restrictWith restrictConcS

/-! ## 4. The restricted closure -/

section ClosureR
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → (PFact × AFact) → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- The result of a restricted run: the least set of objects closed under the rules.
    Rules as in `D`, except `initR` (in place of `initA`), `ret` (restricted, `sat`) and
    `retRec` (persisted records). -/
inductive DR : Obj → Prop where
  | root {M} : M ∈ roots → DR (.init M zeroFact)
  | start {M i} : DR (.init M i) → DR (.edge M i (P.entry M) (startFact i))
  | step {M i n f n' s f'} :
      DR (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transfer counted L s f).facts → DR (.edge M i n' f')
  | reqStmt {M i n f n' s t} :
      DR (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      t ∈ (transfer counted L s f).reqs → DR (.req M i t)
  | pass {M i n f n' c} :
      DR (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      memB f.fact.base c.touched = false → DR (.edge M i n' f)
  | added {M i n f n' c e a} :
      DR (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      DR (.added c.callee a.fact)
  -- the abstraction follows the demand: only the emission table creates initial facts
  | initR {m a d j} :
      DR (.added m a) → demand m d → emit d.din a = some j → DR (.init m j)
  -- a summary edge of the callee, restricted by a demand edge of the callee
  | ret {M i n f n' c e1 a j g d g' r e2 r'} :
      DR (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      DR (.init c.callee j) →
      DR (.edge c.callee j (P.exit c.callee) g) →
      demand c.callee d → restrict j g d = some g' →
      sat j a.fact = true →
      r ∈ (applySummary a j g').facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DR (.edge M i n' (limitF counted L r'))
  -- a persisted complete record of the callee. A record can always be reused (the user's
  -- decision): it applies if the caller fact satisfies its premise (`sat`), OR if the premise
  -- covers the caller fact (`applicable`, the run-1 direction). A record is exact (a normal-layer
  -- edge of an earlier run, `RExact.RecsExact`), so both applications are exact.
  | retRec {M i n f n' c e1 a j g r e2 r'} :
      DR (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      recs c.callee (j, g) → (sat j a.fact = true ∨ applicable j a.fact = true) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DR (.edge M i n' (limitF counted L r'))
  | reqSink {M i n f s t} :
      DR (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .request t →
      DR (.req M i t)
  | answer {M i t a} :
      DR (.req M i t) → DR (.added M a) → a.mark = .conc t →
      overlapB a i = true → DR (.init M (answerInit i a t))
  | reqUp {m j t M ic n f n' c e a} :
      DR (.req m j t) → DR (.edge M ic n f) → (M, n, Instr.call c, n') ∈ P.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      climbsB a.fact.mark t = true → overlapB a.fact j = true → DR (.req M ic t)
  | vuln {M i n f s} :
      DR (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .triggered →
      DR (.vuln M n s f.demand)
  | clean {M i n f n' cl f'} :
      DR (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      f' ∈ (cleanRes cl f).facts → DR (.edge M i n' f')
  | reqClean {M i n f n' cl t} :
      DR (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      t ∈ (cleanRes cl f).reqs → DR (.req M i t)
  | filt {M i n f n' b may} :
      DR (.edge M i n f) → (M, n, Instr.filt b may, n') ∈ P.edges →
      (f.fact.base = b → may f.fact.path = true) → DR (.edge M i n' f)

end ClosureR

/-! ## 5. Demanded flows -/

/-- A concrete flow whose every callee sub-flow is DEMANDED: one demand edge of the callee
    has an entry pattern that covers the entry location (with its mark) and an exit pattern
    that covers the exit location (marks ignored: the restriction reads locations only). -/
inductive FlowR (P : Program) (demand : MethodId → DemandEdge → Prop) :
    MethodId → Loc → Node → Loc → Prop where
  | start (M : MethodId) (l0 : Loc) : FlowR P demand M l0 (P.entry M) l0
  | step {M l0 n l n' l' s} :
      FlowR P demand M l0 n l → (M, n, Instr.stmt s, n') ∈ P.edges → s.step l l' →
      FlowR P demand M l0 n' l'
  | pass {M l0 n l n' c} :
      FlowR P demand M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      memB l.base c.touched = false → FlowR P demand M l0 n' l
  | call {M l0 n l n' c e1 e2 l1 l2 l3 d p} :
      FlowR P demand M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      FlowR P demand c.callee l1 (P.exit c.callee) l2 →
      demand c.callee d → d.din.covers l1 → d.dout = some p → p.coversLoc l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowR P demand M l0 n' l3
  | clean {M l0 n l n' cl} :
      FlowR P demand M l0 n l → (M, n, Instr.clean cl, n') ∈ P.edges →
      cl.cleansB l = false → FlowR P demand M l0 n' l
  | filt {M l0 n l n' b may} :
      FlowR P demand M l0 n l → (M, n, Instr.filt b may, n') ∈ P.edges →
      (l.base = b → may l.path = true) → FlowR P demand M l0 n' l

/-- A concrete vulnerability witness whose every step is demanded: each call down enters
    a location that a demand entry pattern of the callee covers (with its mark). -/
inductive ReachR (P : Program) (demand : MethodId → DemandEdge → Prop) (roots : List MethodId) :
    MethodId → Node → Loc → Prop where
  | root {M n l} : M ∈ roots → FlowR P demand M zeroLoc n l → ReachR P demand roots M n l
  | down {M n l n' c e l1 n2 l2 d} :
      ReachR P demand roots M n l → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → den e.1 e.2 l l1 →
      demand c.callee d → d.din.covers l1 →
      FlowR P demand c.callee l1 n2 l2 → ReachR P demand roots c.callee n2 l2

/-! ## 6. The contracts -/

/-- The emission contract (for every added fact): for a demanded location `l` (with its mark)
    that the added fact `a` carries, the emission gives an initial fact that covers `l` and that
    `a` satisfies. The version-3 tables satisfy it. -/
def EmitContract (emit : PFact → PFact → Option PFact) (sat : PFact → PFact → Bool) : Prop :=
  ∀ d a l, d.covers l → a.covers l →
    ∃ j, emit d a = some j ∧ j.covers l ∧ sat j a = true

/-- The emission contract for CONCRETE added facts only. `emitM` satisfies it. -/
def EmitContractConc (emit : PFact → PFact → Option PFact) (sat : PFact → PFact → Bool) : Prop :=
  ∀ d a l t, a.mark = .conc t → d.covers l → a.covers l →
    ∃ j, emit d a = some j ∧ j.covers l ∧ sat j a = true

/-- The emission contract for the added facts of one run `R` (the closure). The coverage theorem
    of a restricted run needs only this. -/
def EmitContractOn (R : Obj → Prop) (emit : PFact → PFact → Option PFact)
    (sat : PFact → PFact → Bool) : Prop :=
  ∀ m d a l, R (.added m a) → d.covers l → a.covers l →
    ∃ j, emit d a = some j ∧ j.covers l ∧ sat j a = true

/-- The full contract gives the contract for every run. -/
theorem EmitContract.on {emit : PFact → PFact → Option PFact} {sat : PFact → PFact → Bool}
    (h : EmitContract emit sat) (R : Obj → Prop) : EmitContractOn R emit sat :=
  fun _ d a l _ hd ha => h d a l hd ha

/-- The contract for concrete added facts gives the contract for every run whose added facts are
    concrete. -/
theorem EmitContractConc.on {emit : PFact → PFact → Option PFact} {sat : PFact → PFact → Bool}
    (h : EmitContractConc emit sat) {R : Obj → Prop}
    (hc : ∀ m a, R (.added m a) → ∃ t, a.mark = .conc t) : EmitContractOn R emit sat :=
  fun m d a l hR hd ha =>
    match hc m a hR with
    | ⟨t, ht⟩ => h d a l t ht hd ha

/-- A mark-copying emission (`emitM`): the emitted fact has the mark of the added fact. -/
def EmitCopiesMark (emit : PFact → PFact → Option PFact) : Prop :=
  ∀ d a j, emit d a = some j → j.mark = a.mark

/-- The satisfaction contract: a satisfied premise raises no mark request (its mark admits
    the fact mark), and the answer of a request keeps the satisfaction. -/
def SatContract (sat : PFact → PFact → Bool) : Prop :=
  (∀ j a, sat j a = true → markSubB j.mark a.mark = true) ∧
  (∀ j a t, sat j a = true → a.mark = .conc t → sat (answerInit j a t) a = true)

/-- The restriction contract: a demanded pair of a summary edge survives the restriction,
    in the same layer. -/
def RestrictContract (restrict : PFact → AFact → DemandEdge → Option AFact) : Prop :=
  ∀ j g d p l1 l2, den j g.fact l1 l2 → d.din.coversLoc l1 → d.dout = some p →
    p.coversLoc l2 →
    ∃ g', restrict j g d = some g' ∧ den j g'.fact l1 l2 ∧ g'.demand = g.demand

/-- The restriction only removes pairs, and keeps the layer (used for exactness). -/
def RestrictSub (restrict : PFact → AFact → DemandEdge → Option AFact) : Prop :=
  ∀ j g d g', restrict j g d = some g' →
    g'.demand = g.demand ∧ ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2

/-! ## 7. The demand of a run, and the run sequence -/

/-- The demand that a forward run passes on: every initial fact of a method, with each of
    its exit edges (or with no exit). This is the identity backward step; the real backward
    run must keep at least the edges on the witnesses (`BackwardContract`). -/
def summaryDemand (P : Program) (R : Obj → Prop) (m : MethodId) (d : DemandEdge) : Prop :=
  R (.init m d.din) ∧ (d.dout = none ∨ ∃ g, R (.edge m d.din (P.exit m) g) ∧ d.dout = some g.fact)

/-- The contract of the backward run between forward run k and forward run k+1: every
    VULNERABILITY witness (a location at a sink node that the sink pattern covers) that the
    summaries of run k carry stays demanded. Only sink witnesses: a backward run starts at the
    sinks, so it cannot keep the other witnesses (and the iteration does not need them). -/
def BackwardContract (P : Program) (roots : List MethodId) (sinks : List (MethodId × Node × PFact))
    (Rk : Obj → Prop) (dnext : MethodId → DemandEdge → Prop) : Prop :=
  ∀ M n l s T, (M, n, s) ∈ sinks → s.mark = .conc T → s.covers l →
    ReachR P (summaryDemand P Rk) roots M n l → ReachR P dnext roots M n l

end ApSpec
