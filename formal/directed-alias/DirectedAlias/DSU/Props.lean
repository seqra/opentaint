import DirectedAlias.DSU.Model

/-!
# The DSU answer is an equivalence relation

The DSU answer `dsuMayD` relates two access paths when a prefix of each path has the same group
and the rest is the same suffix. It is reflexive (on paths whose base has a group), symmetric,
transitive, and closed under extension. Thus it can never give the directed answer of the task
(`x ~ a`, `a ~ y`, but not `x ~ y`).
-/

namespace DirectedAlias.DSU

open DirectedAlias

/-- The Prop form of the DSU answer: a split of both paths into a prefix with one group and a
common suffix. -/
def DMay (D : DState) (x : Var) (px : List Acc) (y : Var) (py : List Acc) : Prop :=
  ∃ p1 q1 s n, px = p1 ++ s ∧ py = q1 ++ s ∧ matD D x p1 = some n ∧ matD D y q1 = some n

/-- To follow a path in two parts is to follow the first part and then the second part. -/
theorem follow_append (D : DState) :
    ∀ (n : Node) (p q : List Acc), follow D n (p ++ q) = (follow D n p).bind (fun m => follow D m q)
  | n, [], q => by simp [follow]
  | n, c :: cs, q => by
    simp only [List.cons_append, follow]
    cases edgeOf D n c with
    | none => rfl
    | some t => exact follow_append D t cs q

/-- The group of `x.(p ++ q)` is the group of `x.p` followed along `q`. -/
theorem matD_append (D : DState) (x : Var) (p q : List Acc) :
    matD D x (p ++ q) = (matD D x p).bind (fun m => follow D m q) := by
  unfold matD
  cases nodeOf D (.loc x) with
  | none => rfl
  | some n => exact follow_append D n p q

/-- `sameB` is true if and only if the two paths have one group. -/
theorem sameB_iff {D : DState} {x y : Var} {px py : List Acc} :
    sameB D x px y py = true ↔ ∃ n, matD D x px = some n ∧ matD D y py = some n := by
  unfold sameB
  cases h1 : matD D x px with
  | none => simp
  | some n =>
    cases h2 : matD D y py with
    | none => simp
    | some m =>
      simp only [decide_eq_true_eq, Option.some.injEq]
      constructor
      · intro h; exact ⟨n, rfl, h ▸ rfl⟩
      · rintro ⟨k, rfl, rfl⟩; rfl

/-- A list whose reverse ends with `b` starts with `b`. -/
theorem rev_concat {l L : List Acc} {b : Acc} (h : l.reverse = L ++ [b]) :
    l = b :: L.reverse := by
  have := congrArg List.reverse h
  simpa using this

/-- `mayRev` decides the split form on reversed paths. -/
theorem mayRev_iff (D : DState) (x y : Var) :
    ∀ (rx ry : List Acc), mayRev D x y rx ry = true ↔
      ∃ p1 q1 s n, rx.reverse = p1 ++ s ∧ ry.reverse = q1 ++ s ∧
        matD D x p1 = some n ∧ matD D y q1 = some n
  | rx, ry => by
    unfold mayRev
    rw [Bool.or_eq_true]
    constructor
    · rintro (h | h)
      · obtain ⟨n, h1, h2⟩ := sameB_iff.mp h
        exact ⟨rx.reverse, ry.reverse, [], n, by simp, by simp, h1, h2⟩
      · match rx, ry, h with
        | c :: rx', d :: ry', h =>
          rw [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨rfl, h⟩ := h
          obtain ⟨p1, q1, s, n, e1, e2, m1, m2⟩ := (mayRev_iff D x y rx' ry').mp h
          exact ⟨p1, q1, s ++ [c], n, by simp [e1], by simp [e2], m1, m2⟩
    · rintro ⟨p1, q1, s, n, e1, e2, m1, m2⟩
      rcases List.eq_nil_or_concat s with hs | ⟨s', b, hs⟩
      · subst hs
        left
        simp only [List.append_nil] at e1 e2
        exact sameB_iff.mpr ⟨n, e1 ▸ m1, e2 ▸ m2⟩
      · right
        simp only [List.concat_eq_append] at hs
        subst hs
        have r1 := rev_concat (l := rx) (L := p1 ++ s') (b := b) (by simpa using e1)
        have r2 := rev_concat (l := ry) (L := q1 ++ s') (b := b) (by simpa using e2)
        subst r1 r2
        simp only [decide_true, Bool.true_and]
        exact (mayRev_iff D x y _ _).mpr ⟨p1, q1, s', n, by simp, by simp, m1, m2⟩

/-- `dsuMayD` decides `DMay`. -/
theorem dsuMayD_iff {D : DState} {x y : Var} {px py : List Acc} :
    dsuMayD D x px y py = true ↔ DMay D x px y py := by
  unfold dsuMayD DMay
  rw [mayRev_iff]
  simp only [List.reverse_reverse]

/-- The DSU answer is reflexive on each path whose base variable has a group. -/
theorem DMay.refl {D : DState} {x : Var} {n : Node} (h : nodeOf D (.loc x) = some n)
    (p : List Acc) : DMay D x p x p :=
  ⟨[], [], p, n, rfl, rfl, by simp [matD, h, follow], by simp [matD, h, follow]⟩

/-- The DSU answer is symmetric. -/
theorem DMay.symm {D : DState} {x y : Var} {px py : List Acc} (h : DMay D x px y py) :
    DMay D y py x px := by
  obtain ⟨p1, q1, s, n, e1, e2, m1, m2⟩ := h
  exact ⟨q1, p1, s, n, e2, e1, m2, m1⟩

/-- The DSU answer is transitive. -/
theorem DMay.trans {D : DState} {x y z : Var} {px py pz : List Acc}
    (h1 : DMay D x px y py) (h2 : DMay D y py z pz) : DMay D x px z pz := by
  obtain ⟨p1, q1, s1, n, e1, e2, m1, m2⟩ := h1
  obtain ⟨q2, r2, s2, m, f1, f2, k1, k2⟩ := h2
  rw [e2] at f1
  rcases List.append_eq_append_iff.mp f1 with ⟨as, hq2, hs1⟩ | ⟨bs, hq1, hs2⟩
  · subst hq2 hs1
    rw [matD_append, m2] at k1
    refine ⟨p1 ++ as, r2, s2, m, by simp [e1], f2, ?_, k2⟩
    rw [matD_append, m1]; exact k1
  · subst hq1 hs2
    rw [matD_append, k1] at m2
    refine ⟨p1, r2 ++ bs, s1, n, e1, by simp [f2], m1, ?_⟩
    rw [matD_append, k2]; exact m2

/-- The DSU answer is closed under extension by one accessor (congruence). -/
theorem DMay.ext {D : DState} {x y : Var} {px py : List Acc} (c : Acc)
    (h : DMay D x px y py) : DMay D x (px ++ [c]) y (py ++ [c]) := by
  obtain ⟨p1, q1, s, n, e1, e2, m1, m2⟩ := h
  exact ⟨p1, q1, s ++ [c], n, by simp [e1], by simp [e2], m1, m2⟩

/-- The DSU answer is never directed: if `x ~ a` and `a ~ y`, then `x ~ y`. -/
theorem dsu_never_directed (D : DState) (x a y : Var) (px pa py : List Acc) :
    ¬ (dsuMayD D x px a pa = true ∧ dsuMayD D a pa y py = true ∧ dsuMayD D x px y py = false) := by
  rintro ⟨h1, h2, h3⟩
  have := dsuMayD_iff.mpr (DMay.trans (dsuMayD_iff.mp h1) (dsuMayD_iff.mp h2))
  rw [h3] at this
  cases this

/-- The DSU answer at the end of a program is never directed. -/
theorem dsuMay_never_directed (cfg : DCfg) (fr : Frame) (p : Prog) (x a y : Var)
    (px pa py : List Acc) :
    ¬ (dsuMay cfg fr p x px a pa = true ∧ dsuMay cfg fr p a pa y py = true ∧
      dsuMay cfg fr p x px y py = false) := by
  unfold dsuMay
  cases dsuProg cfg fr p with
  | none => simp
  | some D => exact dsu_never_directed D x a y px pa py

/-- The faithful query limit: the reported prefix has at most `L` accessors
(`HEAP_CHAIN_LIMIT = 5` gives `L = 6`). -/
def DMayL (L : Nat) (D : DState) (x : Var) (px : List Acc) (y : Var) (py : List Acc) : Prop :=
  ∃ p1 q1 s n, px = p1 ++ s ∧ py = q1 ++ s ∧ p1.length ≤ L ∧ q1.length ≤ L ∧
    matD D x p1 = some n ∧ matD D y q1 = some n

/-- For paths of length at most `L`, the limit does not change the answer. -/
theorem DMayL_iff_short {L : Nat} {D : DState} {x y : Var} {px py : List Acc}
    (hx : px.length ≤ L) (hy : py.length ≤ L) : DMayL L D x px y py ↔ DMay D x px y py := by
  constructor
  · rintro ⟨p1, q1, s, n, e1, e2, _, _, m1, m2⟩; exact ⟨p1, q1, s, n, e1, e2, m1, m2⟩
  · rintro ⟨p1, q1, s, n, e1, e2, m1, m2⟩
    refine ⟨p1, q1, s, n, e1, e2, ?_, ?_, m1, m2⟩
    · have := congrArg List.length e1; simp at this; omega
    · have := congrArg List.length e2; simp at this; omega

end DirectedAlias.DSU
