/-
  ApSpec.FlowGroupIncremental — rule P3 of spec/next-iteration-p1-p3.md: incremental
  canonicalization in `FlowGroup.addAll` (ap/Groups.kt).

  Model. A row is (id, header, positions). The production row is a FLOW trie with a header
  (tail, E, mark exclusion); the positions are its leaf paths, the id is the object identity
  (`it !== row`). Two relations are parameters:
    * `covAt hs q ht p`: a stored leaf at `q` under header `hs` covers the position `p` of a row with
      header `ht` (`FlowGroup.subtractSubsumed` / `LeafAlgebra.subtract`: the `at` leaf when `q = p`,
      the `below` leaf through an admitted first step when `q` is a strict prefix of `p`);
    * `dom h q p`: a leaf at `q` of the same row covers `p` (`compactPacket`).
  `covers s h p` is the disjunction over the positions of `s`. This is the modelling step: the trie
  subtraction is pointwise, so the cover of one position is the union over the stored leaves.

  `pass L` is one full pass of `addAll` (Groups.kt, the `mapNotNull` over all rows):
  row := compact(row) minus every position that another row covers; an empty row goes.

  Theorems.
    * `pass_out_clean`: a row of `pass L` is compact and no other row of `pass L` covers it.
    * `pass_idem`: `pass (pass L) = pass L`. So the final pass of `addAll` after the loop is a
      no-op (the loop ends right after a pass), and the stored list is a fixpoint of the pass.
    * `passInc_eq`: when the `clean` rows are compact and pairwise not covered, the pass that
      subtracts only the non-clean rows from a clean row equals the full pass.
    * `exit_fixpoint`: the list that `addAll` stores is a fixpoint (pass, merge and promotion change
      nothing).
    * `loopInc_eq`, `addAllInc_eq`: the P3 `addAll` (early return when the insert changes nothing,
      incremental passes, no final pass) gives the native list on every stored fixpoint.

  Constructive: no classical axioms beyond `propext` (simp).
-/

namespace ApSpec.FlowGroupInc

variable {Pos H : Type}

structure Row (Pos H : Type) where
  id  : Nat
  hdr : H
  pos : List Pos
deriving DecidableEq

variable (covAt : H → Pos → H → Pos → Bool) (dom : H → Pos → Pos → Bool)

/-- The stored row `s` covers the position `p` of a row with header `h`. -/
def covers (s : Row Pos H) (h : H) (p : Pos) : Bool := s.pos.any (fun q => covAt s.hdr q h p)

/-- `compactPacket`: drop a position that another leaf of the same row covers. -/
def compact (r : Row Pos H) : Row Pos H :=
  ⟨r.id, r.hdr, r.pos.filter (fun p => !(r.pos.any (fun q => dom r.hdr q p)))⟩

/-- Some row of `L` with another identity covers `p` of `r`. -/
def coveredBy (L : List (Row Pos H)) (r : Row Pos H) (p : Pos) : Bool :=
  L.any (fun s => s.id != r.id && covers covAt s r.hdr p)

/-- One row of the full pass. -/
def passRow (L : List (Row Pos H)) (r : Row Pos H) : Option (Row Pos H) :=
  let ps := (compact dom r).pos.filter (fun p => !(coveredBy covAt L r p))
  if ps.isEmpty then none else some ⟨r.id, r.hdr, ps⟩

/-- The full pass of `FlowGroup.addAll`. -/
def pass (L : List (Row Pos H)) : List (Row Pos H) := L.filterMap (passRow covAt dom L)

/-- Rows of `L` that are compact and that no other row of `L` covers. -/
def Clean (L : List (Row Pos H)) (r : Row Pos H) : Prop :=
  compact dom r = r ∧ ∀ p ∈ r.pos, coveredBy covAt L r p = false

theorem filterMap_self {α : Type} (f : α → Option α) :
    ∀ (l : List α), (∀ x ∈ l, f x = some x) → l.filterMap f = l
  | [], _ => rfl
  | x :: xs, h => by
    have hx : f x = some x := h x (List.mem_cons_self ..)
    have ih := filterMap_self f xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp [hx, ih]

theorem filterMap_congr' {α β : Type} (f g : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
    have hx : f x = g x := h x (List.mem_cons_self ..)
    have ih := filterMap_congr' f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [List.filterMap_cons, List.filterMap_cons, hx, ih]

theorem any_mono {α : Type} (l m : List α) (g : α → Bool) (hsub : ∀ x ∈ l, x ∈ m)
    (h : l.any g = true) : m.any g = true := by
  rw [List.any_eq_true] at h ⊢
  obtain ⟨x, hx, hg⟩ := h
  exact ⟨x, hsub x hx, hg⟩

/-- What a row of the pass is made of. -/
theorem mem_pass {L : List (Row Pos H)} {r' : Row Pos H} (h : r' ∈ pass covAt dom L) :
    ∃ r ∈ L, r'.id = r.id ∧ r'.hdr = r.hdr ∧ r'.pos ≠ [] ∧
      ∀ p ∈ r'.pos, p ∈ r.pos ∧ (r.pos.any (fun q => dom r.hdr q p)) = false ∧
        coveredBy covAt L r p = false := by
  unfold pass at h
  rw [List.mem_filterMap] at h
  obtain ⟨r, hr, hf⟩ := h
  unfold passRow at hf
  simp only at hf
  split at hf
  · cases hf
  · rename_i hne
    cases hf
    refine ⟨r, hr, rfl, rfl, ?_, ?_⟩
    · intro he
      apply hne
      simp only at he
      rw [he]
      rfl
    · intro p hp
      simp only [List.mem_filter, compact] at hp
      obtain ⟨⟨hpr, hdom⟩, hcov⟩ := hp
      refine ⟨hpr, ?_, ?_⟩
      · simpa using hdom
      · simpa using hcov

/-- A row of the pass is covered by no other row of the pass (covers is monotone in positions). -/
theorem pass_not_covered {L : List (Row Pos H)} {r' : Row Pos H} (h : r' ∈ pass covAt dom L) :
    ∀ p ∈ r'.pos, coveredBy covAt (pass covAt dom L) r' p = false := by
  obtain ⟨r, _, hid, hhdr, _, hpos⟩ := mem_pass covAt dom h
  intro p hp
  obtain ⟨_, _, hcov⟩ := hpos p hp
  cases hc : coveredBy covAt (pass covAt dom L) r' p
  · rfl
  · exfalso
    unfold coveredBy at hc
    rw [List.any_eq_true] at hc
    obtain ⟨s', hs', hs'c⟩ := hc
    obtain ⟨s, hs, sid, shdr, _, spos⟩ := mem_pass covAt dom hs'
    have hne : (s'.id != r'.id) = true := by
      simp only [Bool.and_eq_true] at hs'c
      exact hs'c.1
    have hcs' : covers covAt s' r'.hdr p = true := by
      simp only [Bool.and_eq_true] at hs'c
      exact hs'c.2
    have hcs : covers covAt s r.hdr p = true := by
      unfold covers at hcs' ⊢
      rw [← shdr, ← hhdr]
      exact any_mono _ _ _ (fun q hq => (spos q hq).1) hcs'
    have : coveredBy covAt L r p = true := by
      unfold coveredBy
      rw [List.any_eq_true]
      refine ⟨s, hs, ?_⟩
      simp only [Bool.and_eq_true]
      refine ⟨?_, hcs⟩
      rw [← sid, ← hid]
      exact hne
    rw [hcov] at this
    cases this

/-- A row of the pass is compact. -/
theorem pass_compact {L : List (Row Pos H)} {r' : Row Pos H} (h : r' ∈ pass covAt dom L) :
    compact dom r' = r' := by
  obtain ⟨r, _, _, hhdr, _, hpos⟩ := mem_pass covAt dom h
  unfold compact
  have hf : r'.pos.filter (fun p => !(r'.pos.any (fun q => dom r'.hdr q p))) = r'.pos := by
    rw [List.filter_eq_self]
    intro p hp
    obtain ⟨_, hdom, _⟩ := hpos p hp
    cases hd : r'.pos.any (fun q => dom r'.hdr q p)
    · rfl
    · exfalso
      have : r.pos.any (fun q => dom r.hdr q p) = true := by
        rw [← hhdr]
        exact any_mono _ _ _ (fun q hq => (hpos q hq).1) hd
      rw [hdom] at this
      cases this
  rw [hf]

theorem pass_out_clean {L : List (Row Pos H)} {r' : Row Pos H} (h : r' ∈ pass covAt dom L) :
    Clean covAt dom (pass covAt dom L) r' :=
  ⟨pass_compact covAt dom h, pass_not_covered covAt dom h⟩

/-- A clean row is kept by the pass unchanged. -/
theorem passRow_clean {L : List (Row Pos H)} {r : Row Pos H} (hc : Clean covAt dom L r)
    (hne : r.pos ≠ []) : passRow covAt dom L r = some r := by
  obtain ⟨hcomp, hcov⟩ := hc
  unfold passRow
  simp only
  rw [hcomp]
  have hf : r.pos.filter (fun p => !(coveredBy covAt L r p)) = r.pos := by
    rw [List.filter_eq_self]
    intro p hp
    simp [hcov p hp]
  rw [hf]
  have : r.pos.isEmpty = false := by
    cases hp : r.pos
    · exact absurd hp hne
    · rfl
  simp [this]

/-- The pass is idempotent. -/
theorem pass_idem (L : List (Row Pos H)) : pass covAt dom (pass covAt dom L) = pass covAt dom L := by
  unfold pass
  apply filterMap_self
  intro r' hr'
  have hc := pass_out_clean covAt dom hr'
  obtain ⟨_, _, _, _, hne, _⟩ := mem_pass covAt dom hr'
  exact passRow_clean covAt dom hc hne

/-- The incremental pass of P3: a clean row is subtracted only by the rows that are not clean. -/
def passRowInc (L : List (Row Pos H)) (clean : Row Pos H → Bool) (r : Row Pos H) : Option (Row Pos H) :=
  if clean r then
    let ps := r.pos.filter (fun p => !((L.filter (fun s => !clean s)).any
      (fun s => s.id != r.id && covers covAt s r.hdr p)))
    if ps.isEmpty then none else some ⟨r.id, r.hdr, ps⟩
  else passRow covAt dom L r

def passInc (L : List (Row Pos H)) (clean : Row Pos H → Bool) : List (Row Pos H) :=
  L.filterMap (passRowInc covAt dom L clean)

/-- The clean rows are compact and no other clean row covers them. -/
def CleanFamily (L : List (Row Pos H)) (clean : Row Pos H → Bool) : Prop :=
  ∀ r ∈ L, clean r = true → compact dom r = r ∧
    ∀ s ∈ L, clean s = true → s.id ≠ r.id → ∀ p ∈ r.pos, covers covAt s r.hdr p = false

theorem passInc_eq (L : List (Row Pos H)) (clean : Row Pos H → Bool)
    (hfam : CleanFamily covAt dom L clean) : passInc covAt dom L clean = pass covAt dom L := by
  unfold passInc pass
  apply filterMap_congr'
  intro r hr
  unfold passRowInc
  split
  · rename_i hcl
    obtain ⟨hcomp, hpair⟩ := hfam r hr hcl
    unfold passRow
    simp only
    rw [hcomp]
    have hfil : r.pos.filter (fun p => !((L.filter (fun s => !clean s)).any
          (fun s => s.id != r.id && covers covAt s r.hdr p)))
        = r.pos.filter (fun p => !(coveredBy covAt L r p)) := by
      apply List.filter_congr
      intro p hp
      have : (L.filter (fun s => !clean s)).any (fun s => s.id != r.id && covers covAt s r.hdr p)
          = coveredBy covAt L r p := by
        unfold coveredBy
        cases h1 : L.any (fun s => s.id != r.id && covers covAt s r.hdr p)
        · cases h2 : (L.filter (fun s => !clean s)).any (fun s => s.id != r.id && covers covAt s r.hdr p)
          · rfl
          · exfalso
            have := any_mono _ _ _ (fun x hx => (List.mem_filter.mp hx).1) h2
            rw [h1] at this; cases this
        · rw [List.any_eq_true] at h1
          obtain ⟨s, hs, hsc⟩ := h1
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hsc
          cases hcs : clean s
          · rw [List.any_eq_true]
            refine ⟨s, List.mem_filter.mpr ⟨hs, by simp [hcs]⟩, ?_⟩
            simp [hsc.1, hsc.2]
          · exfalso
            have := hpair s hs hcs hsc.1 p hp
            rw [hsc.2] at this; cases this
      rw [this]
    rw [hfil]
  · rfl

/-- The rows of a pass form a clean family (with `clean = membership in the pass`). -/
theorem pass_family (L : List (Row Pos H)) :
    CleanFamily covAt dom (pass covAt dom L) (fun _ => true) := by
  intro r hr _
  refine ⟨pass_compact covAt dom hr, ?_⟩
  intro s hs _ hne p hp
  have h := pass_not_covered covAt dom hr p hp
  unfold coveredBy at h
  cases hcs : covers covAt s r.hdr p
  · rfl
  · exfalso
    have : (pass covAt dom L).any (fun s => s.id != r.id && covers covAt s r.hdr p) = true := by
      rw [List.any_eq_true]
      exact ⟨s, hs, by simp [hne, hcs]⟩
    rw [h] at this; cases this

/-- A sub-list of a clean family is a clean family. -/
theorem family_sub (L M : List (Row Pos H)) (clean : Row Pos H → Bool)
    (hsub : ∀ x ∈ M, x ∈ L) (hfam : CleanFamily covAt dom L clean) :
    CleanFamily covAt dom M clean := by
  intro r hr hcl
  obtain ⟨hcomp, hpair⟩ := hfam r (hsub r hr) hcl
  exact ⟨hcomp, fun s hs hcs hne p hp => hpair s (hsub s hs) hcs hne p hp⟩

/-! ### The loop of `addAll` and the skip

`merge` is `mergeMustOverlap`, `promote` the promotion scan, `insert` the insert of one row
(`none`: no change). The loop runs a pass, then a merge or a promotion followed by an insert,
until neither applies (`fuel` bounds the model; production terminates by the comment on
strictly reduced finite exclusions). -/

variable (merge : List (Row Pos H) → Option (List (Row Pos H)))
variable (promote : List (Row Pos H) → Option (Row Pos H))
variable (insert : List (Row Pos H) → Row Pos H → Option (List (Row Pos H)))

def loop : Nat → List (Row Pos H) → List (Row Pos H)
  | 0, L => pass covAt dom L
  | n + 1, L =>
    let L1 := pass covAt dom L
    match merge L1 with
    | some L2 => loop n L2
    | none =>
      match promote L1 with
      | some t => loop n ((insert L1 t).getD L1)
      | none => L1

/-- A stored list is a fixpoint: the pass, the merge and the promotion change nothing. -/
def Fixpoint (S : List (Row Pos H)) : Prop :=
  pass covAt dom S = S ∧ merge S = none ∧ promote S = none

/-- The loop ends after a pass, so the final pass of native `addAll` is a no-op. -/
theorem final_pass_noop (n : Nat) (L : List (Row Pos H)) :
    pass covAt dom (loop covAt dom merge promote insert n L) = loop covAt dom merge promote insert n L := by
  induction n generalizing L with
  | zero => exact pass_idem covAt dom L
  | succ n ih =>
    simp only [loop]
    split
    · exact ih _
    · split
      · exact ih _
      · exact pass_idem covAt dom L

/-- On a fixpoint the loop returns its input. -/
theorem loop_fixpoint (n : Nat) (S : List (Row Pos H)) (hS : Fixpoint covAt dom merge promote S) :
    loop covAt dom merge promote insert n S = S := by
  obtain ⟨hp, hm, hpr⟩ := hS
  cases n with
  | zero => exact hp
  | succ n => simp [loop, hp, hm, hpr]

/-- The loop reaches its exit (no merge, no promotion) within the fuel. Production has no fuel. -/
def exits : Nat → List (Row Pos H) → Prop
  | 0, _ => False
  | n + 1, L =>
    match merge (pass covAt dom L) with
    | some L2 => exits n L2
    | none =>
      match promote (pass covAt dom L) with
      | some t => exits n ((insert (pass covAt dom L) t).getD (pass covAt dom L))
      | none => True

/-- The invariant: a list that `addAll` stores is a fixpoint. -/
theorem exit_fixpoint (n : Nat) (L : List (Row Pos H)) (h : exits covAt dom merge promote insert n L) :
    Fixpoint covAt dom merge promote (loop covAt dom merge promote insert n L) := by
  induction n generalizing L with
  | zero => exact absurd h id
  | succ n ih =>
    simp only [exits] at h
    simp only [loop]
    split
    · rename_i L2 hm
      rw [hm] at h
      exact ih _ h
    · rename_i hm
      rw [hm] at h
      simp only at h
      split
      · rename_i t hpr
        rw [hpr] at h
        exact ih _ h
      · rename_i hpr
        exact ⟨pass_idem covAt dom L, hm, hpr⟩

/-- Membership in a pass output is a clean family on any list. -/
theorem family_prev [DecidableEq Pos] [DecidableEq H] (X L : List (Row Pos H)) :
    CleanFamily covAt dom L (fun r => decide (r ∈ pass covAt dom X)) := by
  intro r _ hcl
  have hr : r ∈ pass covAt dom X := of_decide_eq_true hcl
  refine ⟨pass_compact covAt dom hr, ?_⟩
  intro s _ hcs hne p hp
  have hs : s ∈ pass covAt dom X := of_decide_eq_true hcs
  exact ((pass_family covAt dom X) r hr rfl).2 s hs rfl hne p hp

/-- The P3 loop: incremental passes; the clean rows are the rows of the previous pass output. -/
def loopInc [DecidableEq Pos] [DecidableEq H] : Nat → (Row Pos H → Bool) → List (Row Pos H) → List (Row Pos H)
  | 0, c, L => passInc covAt dom L c
  | n + 1, c, L =>
    let L1 := passInc covAt dom L c
    let c1 := fun r => decide (r ∈ L1)
    match merge L1 with
    | some L2 => loopInc n c1 L2
    | none =>
      match promote L1 with
      | some t => loopInc n c1 ((insert L1 t).getD L1)
      | none => L1

theorem loopInc_eq [DecidableEq Pos] [DecidableEq H] (n : Nat) (X L : List (Row Pos H)) :
    loopInc covAt dom merge promote insert n (fun r => decide (r ∈ pass covAt dom X)) L
      = loop covAt dom merge promote insert n L := by
  induction n generalizing X L with
  | zero => exact passInc_eq covAt dom L _ (family_prev covAt dom X L)
  | succ n ih =>
    have h1 := passInc_eq covAt dom L _ (family_prev covAt dom X L)
    simp only [loopInc, loop, h1]
    split
    · exact ih L _
    · split
      · exact ih L _
      · rfl

/-- Native `addAll` on a stored list `S`: insert, loop, final pass. -/
def addAllNative (n : Nat) (S : List (Row Pos H)) (t : Row Pos H) : List (Row Pos H) :=
  pass covAt dom (loop covAt dom merge promote insert n ((insert S t).getD S))

/-- P3 `addAll`: return at once when the insert changes nothing; incremental passes with the stored
    rows as the first clean family; no final pass. -/
def addAllInc [DecidableEq Pos] [DecidableEq H] (n : Nat) (S : List (Row Pos H)) (t : Row Pos H) : List (Row Pos H) :=
  match insert S t with
  | none => S
  | some L => loopInc covAt dom merge promote insert n (fun r => decide (r ∈ S)) L

/-- P3 is exact: on every stored fixpoint the P3 `addAll` gives the native list. -/
theorem addAllInc_eq [DecidableEq Pos] [DecidableEq H] (n : Nat) (S : List (Row Pos H)) (t : Row Pos H)
    (hS : Fixpoint covAt dom merge promote S) :
    addAllInc covAt dom merge promote insert n S t = addAllNative covAt dom merge promote insert n S t := by
  unfold addAllInc addAllNative
  split
  · rename_i hins
    rw [hins]
    simp only [Option.getD_none]
    rw [loop_fixpoint covAt dom merge promote insert n S hS]
    exact hS.1.symm
  · rename_i L hins
    rw [hins]
    simp only [Option.getD_some]
    rw [final_pass_noop]
    have hcl : (fun r => decide (r ∈ S)) = (fun r => decide (r ∈ pass covAt dom S)) := by
      rw [hS.1]
    rw [hcl]
    exact loopInc_eq covAt dom merge promote insert n S L

end ApSpec.FlowGroupInc
