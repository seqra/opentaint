/-
  ApSpec.Confirmed — a CONFIRMED vulnerability is a real vulnerability.

  A vulnerability on a complete edge is not enough: a demand caller edge can feed
  an added fact, the callee can answer the request with an exact initial fact
  (normal layer), and the callee sink edge is then complete (review 2).

  The fix: confirmation needs a normal-layer SUPPORT chain from a root (`Sup`).
  Only the zero fact and exact concrete-mark request answers are supported, and
  only through normal-layer caller edges of supported initial facts.

  Main results:
    * `sup_entry`        a supported initial fact is exact with a concrete mark, and
                         its unique location is entry-reachable.
    * `confirmed_real`   a confirmed vulnerability has a concrete witness:
                         `∃ l, Reach P roots M n l ∧ s.covers l`.
                         (`confirmed_real_of`: the same without `P.WF`, which the
                         proof does not use.)
    * `rev2_vuln_derived`, `rev2_not_confirmed`: the false positive of review 2 is
                         derived in the normal layer, but it is not confirmed.
    * `weak_support_gap` the proposed weak side condition admits a false positive.

  Lemma used at the sink: under a non-`*` initial fact every final fact is non-`*`
  (`D_NS`). So a complete final fact under a supported (exact) initial fact is exact,
  and the sink overlap gives a location inside the sink pattern.

  Side condition (correction of the proposed form): the support needs `j = a.fact`.
  The form `j = answerInit k a.fact t ∧ j.kind = .exact` is too weak: the request
  `k` can be on a different base or on a shorter path than the added fact `a`, and
  then `j` denotes a location that `a` does not reach (see `weak_support_gap`).
  For an answer made by the rule `answer` from the same added fact (`overlapB a k`)
  with an exact match, `j = a.fact` is true, so the condition loses no real answer.
-/
import ApSpec.Exact
import ApSpec.Core
import ApSpec.Invariant

namespace ApSpec.Confirmed
open ApSpec

/-! ## 1. Under a non-`*` initial fact every final fact is non-`*` -/

theorem norm_nonstar {x : AFact} (h : x.fact.kind.isStar = false) : x.norm = x := by
  obtain ⟨⟨b, p, k, m⟩, d⟩ := x
  cases k with
  | star e => cases h
  | any => rfl
  | exact => rfl

theorem applyEdge_nonstar {c r : AFact} {fr to : PFact} (hc : c.fact.kind.isStar = false)
    (hr : r ∈ (applyEdge c fr to).facts) : r.fact.kind.isStar = false := by
  obtain ⟨p, k, ap, hg, rfl⟩ := Invariant.applyEdge_shape hr
  have hk : k.isStar = false := Invariant.geo_nonstar hc hg
  rw [norm_nonstar hk]
  exact hk

theorem limitF_nonstar {counted : Acc → Bool} {L : Nat} {f : AFact}
    (h : f.fact.kind.isStar = false) : (limitF counted L f).fact.kind.isStar = false := by
  rcases Invariant.limitF_cases counted L f with e | ⟨hany, _⟩
  · rw [e]; exact h
  · rw [hany]; rfl

theorem startFact_nonstar {i : PFact} (h : i.kind.isStar = false) :
    (startFact i).fact.kind.isStar = false := by
  obtain ⟨b, p, k, m⟩ := i
  cases k with
  | star e => cases h
  | any => cases m <;> rfl
  | exact => rfl

theorem transfer_nonstar {counted : Acc → Bool} {L : Nat} {s : Stmt} {c r : AFact}
    (hc : c.fact.kind.isStar = false) (hr : r ∈ (transfer counted L s c).facts) :
    r.fact.kind.isStar = false := by
  rcases Invariant.transfer_mem hr with rfl | ⟨x, e, _, hx, rfl⟩
  · exact hc
  · exact limitF_nonstar (applyEdge_nonstar hc hx)

/-- The motive: under a non-`*` initial fact the final fact is non-`*`. -/
def NS : Obj → Prop
  | .edge _ i _ f => i.kind.isStar = false → f.fact.kind.isStar = false
  | _ => True

theorem D_NS {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {o : Obj} (h : D P counted L α sinks roots o) : NS o := by
  induction h with
  | root => trivial
  | @start M i _ _ => exact fun hi => startFact_nonstar hi
  | @step M i n f n' s f' _ _ hf' ih => exact fun hi => transfer_nonstar (ih hi) hf'
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ _ _ ha _ _ _ hr _ hr' ihF _ _ =>
    intro hi
    have h1 := applyEdge_nonstar (ihF hi) ha
    obtain ⟨x, hx, rfl⟩ := Invariant.applySummary_shape hr
    have h2 := applyEdge_nonstar h1 hx
    have h3 : (AFact.norm ⟨x.fact, x.demand || g.demand⟩).fact.kind.isStar = false := by
      rw [norm_nonstar (x := ⟨x.fact, x.demand || g.demand⟩) h2]
      exact h2
    exact limitF_nonstar (applyEdge_nonstar h3 hr')
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial

#print axioms D_NS

/-! ## 2. The sink check on an exact initial fact -/

theorem check_triggered {i s : PFact} {f : AFact} {t0 : Mark} (him : i.mark = .conc t0)
    (h : check i f s = .triggered) :
    ∃ T, s.mark = .conc T ∧ overlapB f.fact s = true ∧ f.fact.mark.out t0 = T := by
  unfold check at h
  cases hsm : s.mark with
  | star => rw [hsm] at h; cases h
  | conc T =>
    rw [hsm] at h
    cases ho : overlapB f.fact s with
    | false => rw [ho] at h; cases h
    | true =>
      rw [ho] at h
      refine ⟨T, rfl, rfl, ?_⟩
      cases hfm : f.fact.mark with
      | conc t =>
        rw [hfm] at h
        dsimp only at h
        cases hb : Nat.beq t T with
        | false => rw [hb] at h; cases h
        | true => exact Nat.eq_of_beq_eq_true hb
      | star =>
        rw [hfm, him] at h
        dsimp only at h
        cases hb : Nat.beq t0 T with
        | false => rw [hb] at h; cases h
        | true => exact Nat.eq_of_beq_eq_true hb

#print axioms check_triggered

/-- An exact fact that overlaps a sink pattern lies in the sink pattern. -/
theorem overlap_exact_covers {a s : PFact} (hk : a.kind = .exact) (h : overlapB a s = true)
    (m : Mark) (hm : s.mark.admits m) : s.covers ⟨a.base, a.path, m⟩ := by
  unfold overlapB at h
  cases hb : Nat.beq a.base s.base with
  | false => rw [hb] at h; cases h
  | true =>
    rw [hb] at h
    refine ⟨Nat.eq_of_beq_eq_true hb, ?_, hm⟩
    cases hrel : relate a.path s.path with
    | below r =>
      rw [hrel] at h
      have hr : admitsTailB a.kind r = true := h
      rw [hk] at hr
      cases r with
      | nil =>
        have e := Exact.relate_below hrel
        refine ⟨[], ?_, Exact.tailI_nil _⟩
        show a.path = s.path ++ []
        rw [e, List.append_nil, List.append_nil]
      | cons x r => cases hr
    | above r =>
      rw [hrel] at h
      have hr : admitsTailB s.kind r = true := h
      exact ⟨r, Exact.relate_above hrel, Exact.admitsTailB_tailI hr⟩
    | apart => rw [hrel] at h; cases h

#print axioms overlap_exact_covers

theorem complete_nonstar_exact {f : AFact} (hc : f.complete = true)
    (hs : f.fact.kind.isStar = false) : f.fact.kind = .exact := by
  unfold AFact.complete at hc
  cases hk : f.fact.kind with
  | star e => rw [hk] at hs; cases hs
  | any =>
    rw [hk] at hc
    cases hd : f.demand <;> rw [hd] at hc <;> cases hc
  | exact => rfl

/-- The pair of an initial fact at its own location (`σ = []`) and an exact final fact. -/
theorem den_exact_exact {i a : PFact} {t0 : Mark} (him : i.mark = .conc t0)
    (hak : a.kind = .exact) :
    den i a ⟨i.base, i.path, t0⟩ ⟨a.base, a.path, a.mark.out t0⟩ := by
  refine ⟨rfl, rfl, ?_, rfl, [], [], (List.append_nil _).symm, (List.append_nil _).symm,
    Exact.tailI_nil _, ?_⟩
  · rw [him]; exact rfl
  · rw [hak]; exact rfl

/-! ## 3. Entry reachability -/

section
variable (P : Program) (roots : List MethodId)

/-- `EntryReach M l0`: the location `l0` is real at the entry of `M`: the zero
    location of a root, or the binding of a real caller location. -/
def EntryReach (M : MethodId) (l0 : Loc) : Prop :=
  (M ∈ roots ∧ l0 = zeroLoc) ∨
  (∃ M' n l n' c e, Reach P roots M' n l ∧ (M', n, Instr.call c, n') ∈ P.edges ∧
    c.callee = M ∧ e ∈ c.toCallee ∧ den e.1 e.2 l l0)

theorem entry_reach {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (he : EntryReach P roots M l0) (hf : Flow P M l0 n l) : Reach P roots M n l := by
  rcases he with ⟨hM, rfl⟩ | ⟨M', n0, l', n', c, e, hR, hE, rfl, hc, hd⟩
  · exact Reach.root hM hf
  · exact Reach.down hR hE hc hd hf

end

/-! ## 4. Support and confirmation -/

section
variable (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- The normal-layer SUPPORT of initial facts. -/
inductive Sup : MethodId → PFact → Prop where
  | root {M} : M ∈ roots → Sup M zeroFact
  | call {M i n f n' c e a j} :
      Sup M i → D P counted L α sinks roots (.edge M i n f) → f.demand = false →
      (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      D P counted L α sinks roots (.init c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (∃ k t, D P counted L α sinks roots (.req c.callee k t) ∧ a.fact.kind = .exact ∧
          a.fact.mark = .conc t ∧ j = answerInit k a.fact t ∧ j = a.fact)) →
      Sup c.callee j

/-- A CONFIRMED vulnerability: a complete sink edge under a supported initial fact. -/
def Confirmed (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ i f, D P counted L α sinks roots (.edge M i n f) ∧ Sup P counted L α sinks roots M i ∧
    f.complete = true ∧ (M, n, s) ∈ sinks ∧ check i f s = .triggered

end

/-- A supported initial fact is exact with a concrete mark, and its unique location is
    entry-reachable. -/
theorem sup_entry {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {i : PFact}
    (h : Sup P counted L α sinks roots M i) :
    ∃ t, i.kind = .exact ∧ i.mark = .conc t ∧ EntryReach P roots M ⟨i.base, i.path, t⟩ := by
  induction h with
  | root hM => exact ⟨zeroMark, rfl, rfl, Or.inl ⟨hM, rfl⟩⟩
  | @call M i n f n' c e a j _ hD hfd hE he ha had _ hj ih =>
    obtain ⟨t0, hik, him, hent⟩ := ih
    have hJ : ∃ t, a.fact.kind = .exact ∧ a.fact.mark = .conc t ∧ j = a.fact := by
      rcases hj with ⟨hj0, hz⟩ | ⟨k, t, _, hak, ham, _, hja⟩
      · exact ⟨zeroMark, by rw [hz]; rfl, by rw [hz]; rfl, by rw [hj0, hz]⟩
      · exact ⟨t, hak, ham, hja⟩
    obtain ⟨t, hak, ham, rfl⟩ := hJ
    have hden := den_exact_exact (a := a.fact) him hak
    rw [ham] at hden
    obtain ⟨l, hd1, hd2⟩ := Exact.applyEdge_exact hfd ha had hden
    have hR := entry_reach P roots hent (Exact.edge_exact hD hfd hd1)
    exact ⟨t, hak, ham, Or.inr ⟨M, n, l, n', c, e, hR, hE, rfl, he, hd2⟩⟩

#print axioms sup_entry

/-- THE THEOREM (without the well-formedness hypothesis, which it does not need):
    a confirmed vulnerability is a real concrete vulnerability. -/
theorem confirmed_real_of {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {n : Node} {s : PFact}
    (h : Confirmed P counted L α sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨i, f, hD, hS, hc, _, hch⟩ := h
  obtain ⟨t0, hik, him, hent⟩ := sup_entry hS
  have hfd := Exact.complete_demand hc
  have hns : f.fact.kind.isStar = false := D_NS hD (by rw [hik]; rfl)
  have hfk := complete_nonstar_exact hc hns
  obtain ⟨T, hsm, ho, hmo⟩ := check_triggered him hch
  refine ⟨⟨f.fact.base, f.fact.path, f.fact.mark.out t0⟩, ?_, ?_⟩
  · exact entry_reach P roots hent (Exact.edge_exact hD hfd (den_exact_exact him hfk))
  · exact overlap_exact_covers hfk ho _ (by rw [hsm]; exact hmo)

#print axioms confirmed_real_of

/-- THE THEOREM: a confirmed vulnerability is a real concrete vulnerability
    (no false positive). -/
theorem confirmed_real {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {n : Node} {s : PFact}
    (_hwf : P.WF) (h : Confirmed P counted L α sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  confirmed_real_of h

#print axioms confirmed_real

/-! ## 5. The false positive of review 2 is not confirmed

  The program of review 2 (`review2/confirmed_fp.lean`). The analysis derives the
  vulnerability `D (.vuln 1 20 sinkPat false)` (normal layer). Its support chain
  goes through the caller edge `(w,.,$,T2)` at node 3, and that edge is in the
  demand layer. Here we prove the stronger fact: no confirmation is possible,
  because no concrete location reaches the sink. -/

namespace Rev2

def f : Acc := 1
def g : Acc := 2
def T : Mark := 5
def T2 : Mark := 6
def h : Base := 10
def z : Base := 11
def w : Base := 12
def x : Base := 13
def st : Kind := .star Excl.empty
def cnt : Acc → Bool := fun _ => true

-- caller 0: h.f.g = source(T)  (cut to h.f.[any] under L = 1, demand layer)
def s1 : Stmt := ⟨[zeroBase, h], [ (zeroFact, zeroFact),
  (⟨zeroBase, [], .exact, .star⟩, ⟨h, [f, g], .exact, .conc T⟩) ]⟩
-- z = h.f
def s2 : Stmt := ⟨[z, h], [ (⟨h, [], st, .star⟩, ⟨h, [], st, .star⟩),
  (⟨h, [f], st, .star⟩, ⟨z, [], st, .star⟩) ]⟩
-- conditional source: z carries T  =>  w gets T2
def s3 : Stmt := ⟨[z, w], [ (⟨z, [], st, .star⟩, ⟨z, [], st, .star⟩),
  (⟨z, [], .exact, .conc T⟩, ⟨w, [], .exact, .conc T2⟩) ]⟩
-- call m(w); callee 1 has sink(x) for T2 at its entry node
def c1 : Call := ⟨1, [w], [(⟨w, [], st, .star⟩, ⟨x, [], st, .star⟩)], []⟩
def P : Program := ⟨fun m => if m = 0 then 0 else 20, fun m => if m = 0 then 4 else 21,
  [(0, 0, .stmt s1, 1), (0, 1, .stmt s2, 2), (0, 2, .stmt s3, 3), (0, 3, .call c1, 4)]⟩
def sinkPat : PFact := ⟨x, [], .exact, .conc T2⟩
def sinks : List (MethodId × Node × PFact) := [(1, 20, sinkPat)]
def dem : MethodId → List PFact := fun _ => []

/-- The concrete invariant of method 0: no location on `w`; `h` holds only `h.f.g`;
    `z` holds only `z.g`. -/
def Good (l : Loc) : Prop :=
  l.base ≠ w ∧ (l.base = h → l.path = [f, g]) ∧ (l.base = z → l.path = [g])

theorem good_of_base {l : Loc} (hw : l.base ≠ w) (hh : l.base ≠ h) (hz : l.base ≠ z) : Good l :=
  ⟨hw, fun e => absurd e hh, fun e => absurd e hz⟩

theorem step_s1 {l l' : Loc} (hg : Good l) (hs : s1.step l l') : Good l' := by
  rcases hs with ⟨_, rfl⟩ | ⟨e, he, hd⟩
  · exact hg
  · cases he with
    | head =>
      obtain ⟨_, hb, _⟩ := hd
      exact good_of_base (by rw [hb]; decide) (by rw [hb]; decide) (by rw [hb]; decide)
    | tail _ he =>
      cases he with
      | head =>
        obtain ⟨_, hb, _, _, σ, τ, _, hp, _, hτ⟩ := hd
        have hτ' : τ = [] := hτ
        refine ⟨by rw [hb]; decide, fun _ => by rw [hp, hτ']; rfl,
          fun e => absurd (hb.symm.trans e) (by decide)⟩
      | tail _ he => cases he

theorem step_s2 {l l' : Loc} (hg : Good l) (hs : s2.step l l') : Good l' := by
  rcases hs with ⟨_, rfl⟩ | ⟨e, he, hd⟩
  · exact hg
  · cases he with
    | head =>
      obtain ⟨hb0, hb, _, _, σ, τ, hp0, hp, _, hτ, _⟩ := hd
      have hpath : l.path = [f, g] := hg.2.1 hb0
      refine ⟨by rw [hb]; decide, fun _ => ?_, fun e => absurd (hb.symm.trans e) (by decide)⟩
      rw [hp, hτ, ← hpath, hp0]
    | tail _ he =>
      cases he with
      | head =>
        obtain ⟨hb0, hb, _, _, σ, τ, hp0, hp, _, hτ, _⟩ := hd
        have hpath : l.path = [f, g] := hg.2.1 hb0
        rw [hpath] at hp0
        have hσ : σ = [g] := by
          injection hp0 with _ h2
          exact h2.symm
        refine ⟨by rw [hb]; decide, fun e => absurd (hb.symm.trans e) (by decide), fun _ => ?_⟩
        rw [hp, hτ, hσ]; rfl
      | tail _ he => cases he

theorem step_s3 {l l' : Loc} (hg : Good l) (hs : s3.step l l') : Good l' := by
  rcases hs with ⟨_, rfl⟩ | ⟨e, he, hd⟩
  · exact hg
  · cases he with
    | head =>
      obtain ⟨hb0, hb, _, _, σ, τ, hp0, hp, _, hτ, _⟩ := hd
      have hpath : l.path = [g] := hg.2.2 hb0
      refine ⟨by rw [hb]; decide, fun e => absurd (hb.symm.trans e) (by decide), fun _ => ?_⟩
      rw [hp, hτ, ← hpath, hp0]
    | tail _ he =>
      cases he with
      | head =>
        obtain ⟨hb0, _, _, _, σ, τ, hp0, _, hσ, _⟩ := hd
        have hpath : l.path = [g] := hg.2.2 hb0
        have hσ' : σ = [] := hσ
        rw [hpath, hσ'] at hp0
        cases hp0
      | tail _ he => cases he

theorem flow_good {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (hf : Flow P M l0 n l) (h0 : Good l0) : Good l := by
  induction hf with
  | start => exact h0
  | step _ hE hs ih =>
    have ih := ih h0
    cases hE with
    | head => exact step_s1 ih hs
    | tail _ hE =>
      cases hE with
      | head => exact step_s2 ih hs
      | tail _ hE =>
        cases hE with
        | head => exact step_s3 ih hs
        | tail _ hE =>
          cases hE with
          | tail _ hE => cases hE
  | pass _ _ _ ih => exact ih h0
  | call _ hE _ _ _ he2 _ _ _ =>
    cases hE with
    | tail _ hE =>
      cases hE with
      | tail _ hE =>
        cases hE with
        | tail _ hE =>
          cases hE with
          | head => cases he2
          | tail _ hE => cases hE

theorem reach_good {M : MethodId} {n : Node} {l : Loc} (hr : Reach P [0] M n l) :
    M = 0 ∧ Good l := by
  induction hr with
  | root hM hf =>
    cases hM with
    | head => exact ⟨rfl, flow_good hf (good_of_base (by decide) (by decide) (by decide))⟩
    | tail _ hM => cases hM
  | down _ hE he hd _ ih =>
    obtain ⟨rfl, hg⟩ := ih
    cases hE with
    | tail _ hE =>
      cases hE with
      | tail _ hE =>
        cases hE with
        | tail _ hE =>
          cases hE with
          | head =>
            cases he with
            | head => exact absurd hd.1 hg.1
            | tail _ he => cases he
          | tail _ hE => cases hE

/-- The analysis derives the vulnerability in the normal layer (`demand = false`)
    (the derivation of review 2). -/
theorem rev2_vuln_derived : D P cnt 1 (policy dem) sinks [0] (.vuln 1 20 sinkPat false) := by
  have r0 : D P cnt 1 (policy dem) sinks [0] (.init 0 zeroFact) := D.root (by decide)
  have e0 : D P cnt 1 (policy dem) sinks [0] (.edge 0 zeroFact 0 ⟨zeroFact, false⟩) :=
    D.start (P := P) (counted := cnt) (L := 1) (α := policy dem) (sinks := sinks) (roots := [0]) r0
  have e1 : D P cnt 1 (policy dem) sinks [0] (.edge 0 zeroFact 1 ⟨⟨h, [f], .any, .conc T⟩, true⟩) :=
    D.step e0 (s := s1) (List.Mem.head _) (by decide)
  have e2 : D P cnt 1 (policy dem) sinks [0] (.edge 0 zeroFact 2 ⟨⟨z, [], .any, .conc T⟩, true⟩) :=
    D.step e1 (s := s2) (List.Mem.tail _ (List.Mem.head _)) (by decide)
  have e3 : D P cnt 1 (policy dem) sinks [0] (.edge 0 zeroFact 3 ⟨⟨w, [], .exact, .conc T2⟩, true⟩) :=
    D.step e2 (s := s3) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by decide)
  have ad : D P cnt 1 (policy dem) sinks [0] (.added 1 ⟨x, [], .exact, .conc T2⟩) :=
    D.added (a := ⟨⟨x, [], .exact, .conc T2⟩, true⟩) (c := c1) (n' := 4)
      (e := (⟨w, [], st, .star⟩, ⟨x, [], st, .star⟩)) e3
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
      (List.Mem.head _) (by decide)
  have i0 : D P cnt 1 (policy dem) sinks [0] (.init 1 ⟨x, [], st, .star⟩) := by
    have := D.initA ad
    have hp : policy dem 1 ⟨x, [], .exact, .conc T2⟩ = ⟨x, [], st, .star⟩ := by decide
    rw [hp] at this; exact this
  have s0 : D P cnt 1 (policy dem) sinks [0]
      (.edge 1 ⟨x, [], st, .star⟩ 20 ⟨⟨x, [], st, .star⟩, false⟩) := D.start i0
  have rq : D P cnt 1 (policy dem) sinks [0] (.req 1 ⟨x, [], st, .star⟩ T2) :=
    D.reqSink s0 (s := sinkPat) (List.Mem.head _) (by decide)
  have ia : D P cnt 1 (policy dem) sinks [0] (.init 1 ⟨x, [], .exact, .conc T2⟩) :=
    D.answer rq ad rfl (by decide)
  have sa : D P cnt 1 (policy dem) sinks [0]
      (.edge 1 ⟨x, [], .exact, .conc T2⟩ 20 ⟨⟨x, [], .exact, .conc T2⟩, false⟩) := D.start ia
  exact D.vuln sa (s := sinkPat) (List.Mem.head _) (by decide)

#print axioms rev2_vuln_derived

/-- The false positive of review 2 is NOT confirmed. -/
theorem rev2_not_confirmed : ¬ Confirmed P cnt 1 (policy dem) sinks [0] 1 20 sinkPat := by
  intro hc
  obtain ⟨l, hR, _⟩ := confirmed_real_of hc
  exact absurd (reach_good hR).1 (by decide)

#print axioms rev2_not_confirmed

end Rev2

/-! ## 6. The side condition `j = a.fact` is necessary

  The proposed support condition was `j = answerInit k a.fact t ∧ j.kind = .exact`
  (`WeakSup`). It is too weak: the answer `j` of a request `k` on a DIFFERENT base
  is exact, but it does not denote the location that the real added fact `a`
  reaches. Counterexample (a well-formed program): the caller passes a real
  `v/T2` to the parameter `y` and the spurious demand fact `w/T2~` (review 2) to
  the parameter `y2`. The callee has `sink(y2)` for `T2`. The demand fact gives the
  request on `(y2,.,*,*)` and its exact answer `j = (y2,.,$,T2)`. `WeakSup` accepts
  `j` through the real normal fact `a = (y,.,$,T2)` (`answerInit k a T2 = j`,
  `j.kind = $`), so the vulnerability is "confirmed", but `y2` never holds `T2`. -/

section Weak
variable (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- The support with the proposed (weak) side condition `j.kind = .exact`. -/
inductive WeakSup : MethodId → PFact → Prop where
  | root {M} : M ∈ roots → WeakSup M zeroFact
  | call {M i n f n' c e a j} :
      WeakSup M i → D P counted L α sinks roots (.edge M i n f) → f.demand = false →
      (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      D P counted L α sinks roots (.init c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (∃ k t, D P counted L α sinks roots (.req c.callee k t) ∧ a.fact.kind = .exact ∧
          a.fact.mark = .conc t ∧ j = answerInit k a.fact t ∧ j.kind = .exact)) →
      WeakSup c.callee j

def WeakConfirmed (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ i f, D P counted L α sinks roots (.edge M i n f) ∧ WeakSup P counted L α sinks roots M i ∧
    f.complete = true ∧ (M, n, s) ∈ sinks ∧ check i f s = .triggered

end Weak

namespace Weak
open Rev2

def v : Base := 14
def y : Base := 15
def y2 : Base := 16

-- v = source(T2)  (a real normal fact)
def s4 : Stmt := ⟨[zeroBase, v], [ (zeroFact, zeroFact),
  (⟨zeroBase, [], .exact, .star⟩, ⟨v, [], .exact, .conc T2⟩) ]⟩
-- call m(y2 := w, y := v); callee 1 has sink(y2) for T2 at its entry node
def c2 : Call := ⟨1, [w, v], [(⟨w, [], st, .star⟩, ⟨y2, [], st, .star⟩),
  (⟨v, [], st, .star⟩, ⟨y, [], st, .star⟩)], []⟩
def P2 : Program := ⟨fun m => if m = 0 then 0 else 20, fun m => if m = 0 then 5 else 21,
  [(0, 0, .stmt s1, 1), (0, 1, .stmt s2, 2), (0, 2, .stmt s3, 3), (0, 3, .stmt s4, 4),
   (0, 4, .call c2, 5)]⟩
def sinkPat2 : PFact := ⟨y2, [], .exact, .conc T2⟩
def sinks2 : List (MethodId × Node × PFact) := [(1, 20, sinkPat2)]

/-- The answer `j` and the request `k`. -/
def kReq : PFact := ⟨y2, [], st, .star⟩
def jAns : PFact := ⟨y2, [], .exact, .conc T2⟩

theorem P2_wf : P2.WF := by
  refine ⟨?_, ?_, ?_⟩
  · intro M n s n' hE e he
    cases hE with
    | head => cases he with
      | head => rfl
      | tail _ he => cases he with
        | head => rfl
        | tail _ he => cases he
    | tail _ hE => cases hE with
      | head => cases he with
        | head => rfl
        | tail _ he => cases he with
          | head => rfl
          | tail _ he => cases he
      | tail _ hE => cases hE with
        | head => cases he with
          | head => rfl
          | tail _ he => cases he with
            | head => rfl
            | tail _ he => cases he
        | tail _ hE => cases hE with
          | head => cases he with
            | head => rfl
            | tail _ he => cases he with
              | head => rfl
              | tail _ he => cases he
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  · intro M n c n' hE e he
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | head => cases he with
              | head => rfl
              | tail _ he => cases he with
                | head => rfl
                | tail _ he => cases he
            | tail _ hE => cases hE
  · intro M n c n' hE e he
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | head => cases he
            | tail _ hE => cases hE

#print axioms P2_wf

abbrev D2 := D P2 cnt 1 (policy dem) sinks2 [0]

/-- The weak support confirms the vulnerability at `sink(y2)`. -/
theorem weak_confirmed : WeakConfirmed P2 cnt 1 (policy dem) sinks2 [0] 1 20 sinkPat2 := by
  have r0 : D2 (.init 0 zeroFact) := D.root (by decide)
  have e0 : D2 (.edge 0 zeroFact 0 ⟨zeroFact, false⟩) := D.start r0
  have e1 : D2 (.edge 0 zeroFact 1 ⟨⟨h, [f], .any, .conc T⟩, true⟩) :=
    D.step e0 (s := s1) (List.Mem.head _) (by decide)
  have e1z : D2 (.edge 0 zeroFact 1 ⟨zeroFact, false⟩) :=
    D.step e0 (s := s1) (List.Mem.head _) (by decide)
  have e2 : D2 (.edge 0 zeroFact 2 ⟨⟨z, [], .any, .conc T⟩, true⟩) :=
    D.step e1 (s := s2) (List.Mem.tail _ (List.Mem.head _)) (by decide)
  have e2z : D2 (.edge 0 zeroFact 2 ⟨zeroFact, false⟩) :=
    D.step e1z (s := s2) (List.Mem.tail _ (List.Mem.head _)) (by decide)
  have e3 : D2 (.edge 0 zeroFact 3 ⟨⟨w, [], .exact, .conc T2⟩, true⟩) :=
    D.step e2 (s := s3) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by decide)
  have e3z : D2 (.edge 0 zeroFact 3 ⟨zeroFact, false⟩) :=
    D.step e2z (s := s3) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by decide)
  have hE4 : (0, 3, Instr.stmt s4, 4) ∈ P2.edges :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hE5 : (0, 4, Instr.call c2, 5) ∈ P2.edges :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have e4 : D2 (.edge 0 zeroFact 4 ⟨⟨w, [], .exact, .conc T2⟩, true⟩) :=
    D.step e3 (s := s4) hE4 (by decide)
  have e4v : D2 (.edge 0 zeroFact 4 ⟨⟨v, [], .exact, .conc T2⟩, false⟩) :=
    D.step e3z (s := s4) hE4 (by decide)
  -- the spurious added fact y2/T2 (demand) and its request answer j
  have ad : D2 (.added 1 jAns) :=
    D.added (a := ⟨jAns, true⟩) (c := c2) (n' := 5)
      (e := (⟨w, [], st, .star⟩, ⟨y2, [], st, .star⟩)) e4 hE5 (List.Mem.head _) (by decide)
  have i0 : D2 (.init 1 kReq) := by
    have := D.initA ad
    have hp : policy dem 1 jAns = kReq := by decide
    rw [hp] at this; exact this
  have s0 : D2 (.edge 1 kReq 20 ⟨kReq, false⟩) := D.start i0
  have rq : D2 (.req 1 kReq T2) := D.reqSink s0 (s := sinkPat2) (List.Mem.head _) (by decide)
  have ia : D2 (.init 1 jAns) := D.answer rq ad rfl (by decide)
  have sa : D2 (.edge 1 jAns 20 ⟨jAns, false⟩) := D.start ia
  -- the weak support through the REAL normal fact y/T2
  have sup : WeakSup P2 cnt 1 (policy dem) sinks2 [0] 1 jAns := by
    refine WeakSup.call (WeakSup.root (by decide)) e4v rfl hE5
      (e := (⟨v, [], st, .star⟩, ⟨y, [], st, .star⟩))
      (List.Mem.tail _ (List.Mem.head _))
      (a := ⟨⟨y, [], .exact, .conc T2⟩, false⟩) (by decide) rfl ia
      (Or.inr ⟨kReq, T2, rq, rfl, rfl, by decide, rfl⟩)
  exact ⟨jAns, ⟨jAns, false⟩, sa, sup, rfl, List.Mem.head _, by decide⟩

#print axioms weak_confirmed

theorem step_s4 {l l' : Loc} (hg : Good l) (hs : s4.step l l') : Good l' := by
  rcases hs with ⟨_, rfl⟩ | ⟨e, he, hd⟩
  · exact hg
  · cases he with
    | head =>
      obtain ⟨_, hb, _⟩ := hd
      exact good_of_base (by rw [hb]; decide) (by rw [hb]; decide) (by rw [hb]; decide)
    | tail _ he =>
      cases he with
      | head =>
        obtain ⟨_, hb, _⟩ := hd
        exact good_of_base (by rw [hb]; decide) (by rw [hb]; decide) (by rw [hb]; decide)
      | tail _ he => cases he

theorem flow_good2 {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (hf : Flow P2 M l0 n l) (h0 : Good l0) : Good l := by
  induction hf with
  | start => exact h0
  | step _ hE hs ih =>
    have ih := ih h0
    cases hE with
    | head => exact step_s1 ih hs
    | tail _ hE =>
      cases hE with
      | head => exact step_s2 ih hs
      | tail _ hE =>
        cases hE with
        | head => exact step_s3 ih hs
        | tail _ hE =>
          cases hE with
          | head => exact step_s4 ih hs
          | tail _ hE =>
            cases hE with
            | tail _ hE => cases hE
  | pass _ _ _ ih => exact ih h0
  | call _ hE _ _ _ he2 _ _ _ =>
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | head => cases he2
            | tail _ hE => cases hE

/-- Method 1 has no instruction: a flow in it stays at the entry location. -/
theorem flow_callee {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (hf : Flow P2 M l0 n l) (hM : M = 1) : l = l0 := by
  induction hf with
  | start => rfl
  | step _ hE _ _ =>
    subst hM
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | pass _ hE _ _ =>
    subst hM
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | call _ hE _ _ _ _ _ _ _ =>
    subst hM
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE

theorem reach2 {M : MethodId} {n : Node} {l : Loc} (hr : Reach P2 [0] M n l) :
    (M = 0 ∧ Good l) ∨ (M = 1 ∧ l.base = y) := by
  induction hr with
  | root hM hf =>
    cases hM with
    | head => exact Or.inl ⟨rfl, flow_good2 hf (good_of_base (by decide) (by decide) (by decide))⟩
    | tail _ hM => cases hM
  | down _ hE he hd hf ih =>
    rcases ih with ⟨rfl, hg⟩ | ⟨rfl, _⟩
    · cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE with
              | head =>
                cases he with
                | head => exact absurd hd.1 hg.1
                | tail _ he =>
                  cases he with
                  | head =>
                    right
                    refine ⟨rfl, ?_⟩
                    rw [flow_callee hf rfl]
                    exact hd.2.1
                  | tail _ he => cases he
              | tail _ hE => cases hE
    · cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE with
              | tail _ hE => cases hE

/-- The weakly confirmed vulnerability is NOT real: no location reaches `sink(y2)`. -/
theorem weak_not_real : ¬ ∃ l, Reach P2 [0] 1 20 l ∧ sinkPat2.covers l := by
  rintro ⟨l, hR, hc⟩
  rcases reach2 hR with ⟨h1, _⟩ | ⟨_, hb⟩
  · exact absurd h1 (by decide)
  · have hb2 : l.base = y2 := hc.1
    rw [hb] at hb2
    exact absurd hb2 (by decide)

/-- THE GAP: with the weak side condition, `confirmed_real` is false. -/
theorem weak_support_gap :
    P2.WF ∧ WeakConfirmed P2 cnt 1 (policy dem) sinks2 [0] 1 20 sinkPat2 ∧
      ¬ ∃ l, Reach P2 [0] 1 20 l ∧ sinkPat2.covers l :=
  ⟨P2_wf, weak_confirmed, weak_not_real⟩

#print axioms weak_support_gap

end Weak

end ApSpec.Confirmed
