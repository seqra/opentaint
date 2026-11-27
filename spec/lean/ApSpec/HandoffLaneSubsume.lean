/-
  ApSpec.HandoffLaneSubsume — rule H1 of docs/design/owasp-cycle-stirling-split-20261126.md:
  "the hand-off normalizes each TAINT lane of a summary store".

  Production (prototype `driver/ProtoHandoffSubsume.kt`, `ap/Groups.kt` `subsumeTaintLane`): at the
  hand-off read, the DEMAND edges of one store and one premise are grouped by TAINT lane (base,
  layer, protection class). Inside a lane, in a launch-independent order, each row loses the
  coordinates that the other current rows cover (the removal half of the TaintGroup law), until no
  row changes. A row with no coordinate left is removed. Rows are not merged.

  Model: a coordinate is an element of a type `α` (a leaf position with its tail bit); `cov y x`
  says that the coordinate `y` covers `x` (its location set contains the location set of `x`). The
  only hypotheses are that `cov` is reflexive and transitive. A lane is a list of rows; a row is a
  list of coordinates. A pass walks the lane once (`passZ done rest`: the rows in `done` are
  already processed); the step at a row compares it with every other current row.

  This file proves:
  1. NO NEW DEMAND. One step, one pass and the normal form keep every coordinate inside the input
     lane (`step_sub`, `passZ_sub`, `normalize_sub`): H1 only removes coordinates; it never adds a row, a
     coordinate, a layer or a lane.
  2. NO LOST COVERAGE. Every input coordinate is covered by some output coordinate
     (`step_covers`, `passZ_covers`, `normalize_covers`). With the denotation reading of `cov`, the
     union of the location sets of the lane does not change. This is the store subsumption rule of
     ap.md (`[any]` at `p` subsumes every demand fact at or below `p` with its mark).
     NOT CLAIMED: that the C2 starts of the next run stay the same. C2 is not monotone in this
     coverage: its relative cap `FL(Dc)+1` and its EXACT rule depend on the depth and tail of each
     entry `Dc`, so a removed deep EXACT row can take away an EXACT NORMAL start that the covering MAY
     row does not make (reviewer attack 1, design document §9). The same loss occurs in CURRENT when
     the MAY value arrives first, and for every EXACT premise.
  3. A COVERED ROW GOES. If every coordinate of a row is covered by a coordinate of another row,
     the step at that row empties it (`step_removes_covered`). This is the Stirling-PDF row
     `ret.* → {arg(0).X.$}` next to `ret.* → {arg(0).MAY}`.
  4. VECTORS. The Stirling-PDF lane in both arrival orders gives the same normal form (`Vec`).

  Not proved: that the normal form is independent of the order for every input (it is not: of two
  equal rows the later one survives). Production removes the order by a launch-independent sort
  key; the design document lists this as a model difference.

  All proofs are constructive (only `propext`, `Quot.sound`; see the `#print axioms` lines).
-/

namespace ApSpec.HandoffLaneSubsume

section Generic
variable {α : Type} (cov : α → α → Bool)

/-- The coordinate `x` is covered by a coordinate of one of the rows `others`. -/
def coveredBy : List (List α) → α → Bool
  | [], _ => false
  | row :: rows, x => row.any (fun y => cov y x) || coveredBy rows x

/-- The step at `row`, with the other current rows `others`: the row loses the coordinates that the
    other rows cover. -/
def stepRow (others : List (List α)) (row : List α) : List α :=
  row.filter (fun x => !coveredBy cov others x)

/-- One pass over the lane: `done` are the processed rows, `rest` the rows still to process. -/
def passZ : List (List α) → List (List α) → List (List α)
  | done, [] => done
  | done, row :: rest => passZ (done ++ [stepRow cov (done ++ rest) row]) rest

def pass (rows : List (List α)) : List (List α) := passZ cov [] rows

/-- The number of coordinates of a lane. -/
def size : List (List α) → Nat
  | [] => 0
  | row :: rows => row.length + size rows

/-- Repeat passes until the size does not change (at most `fuel` passes). -/
def normalizeF : Nat → List (List α) → List (List α)
  | 0, rows => rows
  | n + 1, rows =>
    let next := pass cov rows
    if size next == size rows then rows else normalizeF n next

def nonEmpty : List α → Bool
  | [] => false
  | _ :: _ => true

/-- The normal form: enough fuel for one removal per pass, empty rows dropped. -/
def normalize (rows : List (List α)) : List (List α) :=
  (normalizeF cov (size rows + 1) rows).filter nonEmpty

/-- A coordinate of a lane. -/
def InLane (rows : List (List α)) (x : α) : Prop := ∃ row ∈ rows, x ∈ row

/-! ## 0. Lane membership -/

theorem inLane_append {a b : List (List α)} {x : α} :
    InLane (a ++ b) x ↔ InLane a x ∨ InLane b x := by
  constructor
  · rintro ⟨row, hrow, hx⟩
    rcases List.mem_append.mp hrow with h | h
    · exact Or.inl ⟨row, h, hx⟩
    · exact Or.inr ⟨row, h, hx⟩
  · rintro (⟨row, hrow, hx⟩ | ⟨row, hrow, hx⟩)
    · exact ⟨row, List.mem_append.mpr (Or.inl hrow), hx⟩
    · exact ⟨row, List.mem_append.mpr (Or.inr hrow), hx⟩

theorem inLane_cons {row : List α} {rows : List (List α)} {x : α} :
    InLane (row :: rows) x ↔ x ∈ row ∨ InLane rows x := by
  constructor
  · rintro ⟨r, hr, hx⟩
    rcases List.mem_cons.mp hr with h | h
    · exact Or.inl (h ▸ hx)
    · exact Or.inr ⟨r, h, hx⟩
  · rintro (hx | ⟨r, hr, hx⟩)
    · exact ⟨row, List.mem_cons_self, hx⟩
    · exact ⟨r, List.mem_cons_of_mem _ hr, hx⟩

theorem coveredBy_spec (others : List (List α)) (x : α) (h : coveredBy cov others x = true) :
    ∃ y, InLane others y ∧ cov y x = true := by
  induction others with
  | nil => exact absurd h Bool.false_ne_true
  | cons row rows ih =>
    simp only [coveredBy, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with ⟨y, hy, hc⟩ | h
    · exact ⟨y, inLane_cons.mpr (Or.inl hy), hc⟩
    · obtain ⟨y, hy, hc⟩ := ih h
      exact ⟨y, inLane_cons.mpr (Or.inr hy), hc⟩

theorem filter_nil_of {p : α → Bool} : ∀ l : List α, (∀ x ∈ l, p x = false) → l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filter_cons, if_neg (by rw [h a List.mem_cons_self]; exact Bool.false_ne_true)]
    exact filter_nil_of l (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ## 1. No new demand -/

theorem stepRow_sub (others : List (List α)) (row : List α) (x : α) :
    x ∈ stepRow cov others row → x ∈ row := fun h => (List.mem_filter.mp h).1

/-- One step keeps every coordinate inside the input lane. -/
theorem step_sub (done rest : List (List α)) (row : List α) (x : α) :
    InLane (done ++ stepRow cov (done ++ rest) row :: rest) x → InLane (done ++ row :: rest) x := by
  intro h
  rcases inLane_append.mp h with h | h
  · exact inLane_append.mpr (Or.inl h)
  · rcases inLane_cons.mp h with h | h
    · exact inLane_append.mpr (Or.inr (inLane_cons.mpr (Or.inl (stepRow_sub cov _ row x h))))
    · exact inLane_append.mpr (Or.inr (inLane_cons.mpr (Or.inr h)))

theorem passZ_sub : ∀ (rest done : List (List α)) (x : α),
    InLane (passZ cov done rest) x → InLane (done ++ rest) x
  | [], done, x, h => by rw [List.append_nil]; exact h
  | row :: rest, done, x, h => by
    have h1 := passZ_sub rest (done ++ [stepRow cov (done ++ rest) row]) x h
    rw [List.append_assoc, List.singleton_append] at h1
    exact step_sub cov done rest row x h1

theorem normalizeF_sub (n : Nat) (rows : List (List α)) (x : α) :
    InLane (normalizeF cov n rows) x → InLane rows x := by
  induction n generalizing rows with
  | zero => exact id
  | succ n ih =>
    intro h
    simp only [normalizeF] at h
    split at h
    · exact h
    · have h1 := passZ_sub cov rows [] x (ih _ h)
      rw [List.nil_append] at h1
      exact h1

/-- THE NO-NEW-DEMAND THEOREM: the normal form has no coordinate that the input lane does not have. -/
theorem normalize_sub (rows : List (List α)) (x : α) :
    InLane (normalize cov rows) x → InLane rows x := by
  rintro ⟨row, hrow, hx⟩
  exact normalizeF_sub cov (size rows + 1) rows x ⟨row, (List.mem_filter.mp hrow).1, hx⟩

/-! ## 2. No lost coverage -/

section Cover
variable (hrefl : ∀ x, cov x x = true)
  (htrans : ∀ x y z, cov z y = true → cov y x = true → cov z x = true)
include hrefl

/-- One step: every coordinate of the input lane is covered by a coordinate of the step result. -/
theorem step_covers (done rest : List (List α)) (row : List α) (x : α)
    (hx : InLane (done ++ row :: rest) x) :
    ∃ y, InLane (done ++ stepRow cov (done ++ rest) row :: rest) y ∧ cov y x = true := by
  rcases inLane_append.mp hx with h | h
  · exact ⟨x, inLane_append.mpr (Or.inl h), hrefl x⟩
  · rcases inLane_cons.mp h with h | h
    · cases hc : coveredBy cov (done ++ rest) x with
      | true =>
        obtain ⟨y, hy, hcy⟩ := coveredBy_spec cov _ x hc
        refine ⟨y, ?_, hcy⟩
        rcases inLane_append.mp hy with hy | hy
        · exact inLane_append.mpr (Or.inl hy)
        · exact inLane_append.mpr (Or.inr (inLane_cons.mpr (Or.inr hy)))
      | false =>
        refine ⟨x, inLane_append.mpr (Or.inr (inLane_cons.mpr (Or.inl ?_))), hrefl x⟩
        exact List.mem_filter.mpr ⟨h, by rw [hc]; rfl⟩
    · exact ⟨x, inLane_append.mpr (Or.inr (inLane_cons.mpr (Or.inr h))), hrefl x⟩

include htrans in
theorem passZ_covers : ∀ (rest done : List (List α)) (x : α), InLane (done ++ rest) x →
    ∃ y, InLane (passZ cov done rest) y ∧ cov y x = true
  | [], done, x, h => ⟨x, by rw [List.append_nil] at h; exact h, hrefl x⟩
  | row :: rest, done, x, h => by
    obtain ⟨y, hy, hyx⟩ := step_covers cov hrefl done rest row x h
    have hy' : InLane ((done ++ [stepRow cov (done ++ rest) row]) ++ rest) y := by
      rw [List.append_assoc, List.singleton_append]; exact hy
    obtain ⟨z, hz, hzy⟩ := passZ_covers rest _ y hy'
    exact ⟨z, hz, htrans x y z hzy hyx⟩

include htrans in
theorem normalizeF_covers (n : Nat) (rows : List (List α)) (x : α) (hx : InLane rows x) :
    ∃ y, InLane (normalizeF cov n rows) y ∧ cov y x = true := by
  induction n generalizing rows x with
  | zero => exact ⟨x, hx, hrefl x⟩
  | succ n ih =>
    simp only [normalizeF]
    split
    · exact ⟨x, hx, hrefl x⟩
    · have hx' : InLane ([] ++ rows) x := by rw [List.nil_append]; exact hx
      obtain ⟨y, hy, hyx⟩ := passZ_covers cov hrefl htrans rows [] x hx'
      obtain ⟨z, hz, hzy⟩ := ih (pass cov rows) y hy
      exact ⟨z, hz, htrans x y z hzy hyx⟩

include htrans in
/-- THE COVERAGE THEOREM: the normal form covers every coordinate of the input lane. -/
theorem normalize_covers (rows : List (List α)) (x : α) (hx : InLane rows x) :
    ∃ y, InLane (normalize cov rows) y ∧ cov y x = true := by
  obtain ⟨y, ⟨row, hrow, hyr⟩, hyx⟩ := normalizeF_covers cov hrefl htrans (size rows + 1) rows x hx
  refine ⟨y, ⟨row, List.mem_filter.mpr ⟨hrow, ?_⟩, hyr⟩, hyx⟩
  cases row with
  | nil => exact absurd hyr List.not_mem_nil
  | cons _ _ => rfl

end Cover

/-! ## 3. A covered row goes -/

/-- If every coordinate of a row is covered by another current row, the step empties that row. -/
theorem step_removes_covered (others : List (List α)) (row : List α)
    (hcov : ∀ x ∈ row, coveredBy cov others x = true) : stepRow cov others row = [] :=
  filter_nil_of row (fun x hx => by rw [hcov x hx]; rfl)

end Generic

/-! ## 4. Vectors: the Stirling-PDF lane (checked by `decide`) -/

namespace Vec
/-- A coordinate: a path below `arg(0)` and the tail bit (`true` = MAY). -/
abbrev Coord := List Nat × Bool
/-- A MAY coordinate covers itself and every coordinate at or below its path; an exact coordinate
    covers only itself. -/
def vcov (y x : Coord) : Bool :=
  (y == x) || (y.2 && y.1.isPrefixOf x.1)
/-- `ret.* → {arg(0).MAY}` and `ret.* → {arg(0).CharSequence#content.$}` (accessor 7). -/
def may : List Coord := [([], true)]
def exact : List Coord := [([7], false)]
/-- The exact row arrives first (slow launch) or second (fast launch): the same normal form. -/
example : normalize vcov [exact, may] = [may] := by decide
example : normalize vcov [may, exact] = [may] := by decide
/-- The +3 form (`arg(0).$`, `Matcher#group.$`, `Matcher#input.$`), in one row. -/
def exact3 : List Coord := [([], false), ([11], false), ([12], false)]
example : normalize vcov [exact3, may] = [may] := by decide
/-- A row that is not covered stays: an exact row under another base path. -/
def other : List Coord := [([9], false)]
example : normalize vcov [exact, other] = [exact, other] := by decide
end Vec

end ApSpec.HandoffLaneSubsume

#print axioms ApSpec.HandoffLaneSubsume.step_sub
#print axioms ApSpec.HandoffLaneSubsume.passZ_sub
#print axioms ApSpec.HandoffLaneSubsume.normalize_sub
#print axioms ApSpec.HandoffLaneSubsume.step_covers
#print axioms ApSpec.HandoffLaneSubsume.passZ_covers
#print axioms ApSpec.HandoffLaneSubsume.normalize_covers
#print axioms ApSpec.HandoffLaneSubsume.step_removes_covered
