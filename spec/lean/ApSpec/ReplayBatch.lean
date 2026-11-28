/-
  ApSpec.ReplayBatch — candidate rule H2 of docs/design/owasp-cycle-stirling-split-20261126.md §6.10:
  "one replay of saved records is one batch".

  Production (prototype `engine/RunMethodCallServices.kt` `flushReplayBatch`, flag
  `org.opentaint.bidi.protoReplayBatch`): CURRENT resumes the caller once per saved record and view,
  in the store order. The statement after the call sends only the fresh part of a fact, and it never
  takes back a fact that it sent (`BlockRunState.admitOutputs`). So a covered result goes on when its
  record replays before the record of its cover. H2 collects the results of all records and views of
  one offer and groups them by lane (caller premise, identity candidate). The results of a lane
  arrive, in one launch-independent general-first order (the shallowest leaf, the wider tail, more
  leaves, the canonical key), at one scratch statement store (`ConclusionGroup`, the store law of a
  restricted run); a result with no fresh part there goes. Then the caller resumes once. A result
  is never cut or merged. This is the landed form (v3, `keepF`, `normalizeF`, `batch`). The
  prototype v2 (`stepWhole`, `normalizeW`, `batchW`) checks each result against all other current
  results of its lane; it needs no order, but its cost is quadratic in the lane size.

  Model: a coordinate is an element of `α`; `cov y x` says that `y` covers `x`. The hypotheses are
  that `cov` is reflexive and transitive. A replay is a list of rows (one row per record, in the
  store order); a row is the list of result coordinates of one record. The statement keeps the list
  of coordinates that it has sent (`store`); an arriving coordinate goes on only when no sent
  coordinate covers it (`sent`, `after`). The order of the rows given to `normalizeF` is the
  general-first order of production (the vectors use `isort`, the shallowest leaf first).

  This file proves:
  0. NORMAL FORMS. `normalizeF` and `normalizeW` keep only coordinates of the replay
     (`normalizeF_sub`, `normalizeW_sub`) and cover every coordinate of the replay
     (`normalizeF_covers`, `normalizeW_covers`). For v2, one pass is a fixpoint
     (`normalizeW_fixpoint`).
  1-4. For EVERY normal form with these two properties (section `Normal`), so for v3 (`h2_*`) and
     v2 (`h2w_eq_cover_first`, and the generic theorems with `normalizeW`):
  1. H2 IS CURRENT WITH THE NORMAL FORM FIRST. The batch sends exactly what CURRENT sends when the
     normal form arrives before all the results of the replay (`batch_eq_cover_first`). This is
     the behaviour of the cheap Stirling-PDF launches, where the cover `ret.MUST` replays first.
  2. NO NEW RESULT. The batch sends only results of the replay (`batch_sub`).
  3. NO LOST COVERAGE, IN EVERY STORE ORDER. After the replay, the sent coordinates of the batch
     and of CURRENT cover each other, whatever the store order of the records
     (`batch_equiv_current`). With the denotation reading of `cov`, both reach the same location
     set at the statement.
  4. ORDER INDEPENDENCE UP TO COVERAGE. Two replays with the same results (in any order) end with
     sent coordinates that cover each other (`batch_perm_equiv`).
  5. VECTORS. The Stirling-PDF lane at `attachment.getFilename()`: CURRENT sends the deep MUST
     results when the deep record replays first and not when the cover replays first; H2 v3 (with
     the general-first order) and v2 send only the cover in both orders; v3 without the order is
     CURRENT again, so the order is part of the rule (`Vec`).

  Exact equality of the sent facts across launches (not only coverage) needs one more fact that
  the model does not state: the order key is a function of the result set. In production the key
  is total up to the canonical key (`replayOrderKey`); the design document lists ties of that key
  as a blind spot.

  NOT CLAIMED: that a statement after the call (cleaner, write of the return value) is monotone in
  coverage. Production compares the facts at the statement store after the call stages; the model
  compares them at the stage input. The store law makes the same assumption at every statement: a
  fact that a stored fact covers never reaches the next statement. The design document lists this as
  a model difference.

  All proofs are constructive (only `propext`, `Quot.sound`; see the `#print axioms` lines).
-/
import ApSpec.HandoffLaneSubsume

namespace ApSpec.ReplayBatch
open ApSpec.HandoffLaneSubsume

section Generic
variable {α : Type} (cov : α → α → Bool)

/-- Some coordinate of `store` covers `x`. -/
def coveredIn (store : List α) (x : α) : Bool := store.any (fun y => cov y x)

/-- The coordinates that the statement sends on when `xs` arrive one at a time after it has sent
    `store` (CURRENT: only a fresh coordinate goes on, and a sent coordinate stays). -/
def sent : List α → List α → List α
  | _, [] => []
  | store, x :: xs => match coveredIn cov store x with
    | true => sent store xs
    | false => x :: sent (x :: store) xs

/-- The coordinates that the statement has sent after the arrivals `xs`. -/
def after : List α → List α → List α
  | store, [] => store
  | store, x :: xs => match coveredIn cov store x with
    | true => after store xs
    | false => after (x :: store) xs

/-- The step at `row`, with the other current rows `others`: the row goes when the other rows cover
    each of its coordinates (the statement store finds no fresh part in it); otherwise it stays whole. -/
def stepWhole (others : List (List α)) (row : List α) : List α :=
  if row.all (fun x => coveredBy cov others x) then [] else row

/-- One pass over the replay: `done` are the processed rows, `rest` the rows still to process. -/
def passW : List (List α) → List (List α) → List (List α)
  | done, [] => done
  | done, row :: rest => passW (done ++ [stepWhole cov (done ++ rest) row]) rest

/-- The normal form of H2: one pass. -/
def normalizeW (rows : List (List α)) : List (List α) := passW cov [] rows

/-- H2 (the landed form): the rows arrive in the given order at one scratch store; a row goes when
    the kept rows cover each of its coordinates (the store finds no fresh part in it); otherwise it
    stays whole. Production gives the rows a launch-independent, general-first order. -/
def keepF : List (List α) → List (List α) → List (List α)
  | kept, [] => kept
  | kept, row :: rest => match row.all (fun x => coveredBy cov kept x) with
    | true => keepF kept rest
    | false => keepF (kept ++ [row]) rest

def normalizeF (rows : List (List α)) : List (List α) := keepF cov [] rows

/-- CURRENT: the caller resumes once per record, in the store order of the rows. -/
def current (store : List α) (rows : List (List α)) : List α := sent cov store rows.flatten

/-- A batch: the replay is one batch, and the normal form `nf` runs on it before the caller resumes. -/
def batchWith (nf : List (List α) → List (List α)) (store : List α) (rows : List (List α)) : List α :=
  sent cov store (nf rows).flatten

/-- H2, the landed form (one scratch store, in the given order). -/
def batch (store : List α) (rows : List (List α)) : List α := batchWith cov (normalizeF cov) store rows

/-- H2 v2, the order-free form (each row against all other current rows; quadratic, not landed). -/
def batchW (store : List α) (rows : List (List α)) : List α := batchWith cov (normalizeW cov) store rows

theorem coveredIn_iff (store : List α) (x : α) :
    coveredIn cov store x = true ↔ ∃ y ∈ store, cov y x = true := by
  unfold coveredIn
  exact List.any_eq_true

theorem inLane_flatten {rows : List (List α)} {x : α} : InLane rows x ↔ x ∈ rows.flatten := by
  constructor
  · rintro ⟨row, hrow, hx⟩; exact List.mem_flatten.mpr ⟨row, hrow, hx⟩
  · intro h; obtain ⟨row, hrow, hx⟩ := List.mem_flatten.mp h; exact ⟨row, hrow, hx⟩

/-! ## 0. The normal form of H2 -/

theorem stepWhole_sub (others : List (List α)) (row : List α) (x : α) :
    x ∈ stepWhole cov others row → x ∈ row := by
  unfold stepWhole
  split
  · intro h; exact absurd h List.not_mem_nil
  · exact id

theorem passW_sub : ∀ (rest done : List (List α)) (x : α),
    InLane (passW cov done rest) x → InLane (done ++ rest) x
  | [], done, x, h => by rw [List.append_nil]; exact h
  | row :: rest, done, x, h => by
    have h1 := passW_sub rest (done ++ [stepWhole cov (done ++ rest) row]) x h
    rw [List.append_assoc, List.singleton_append] at h1
    rcases inLane_append.mp h1 with h | h
    · exact inLane_append.mpr (Or.inl h)
    · rcases inLane_cons.mp h with h | h
      · exact inLane_append.mpr (Or.inr (inLane_cons.mpr (Or.inl (stepWhole_sub cov _ row x h))))
      · exact inLane_append.mpr (Or.inr (inLane_cons.mpr (Or.inr h)))

/-- No new result: the normal form keeps only coordinates of the replay. -/
theorem normalizeW_sub (rows : List (List α)) (x : α) :
    InLane (normalizeW cov rows) x → InLane rows x := by
  intro h
  have h1 := passW_sub cov rows [] x h
  rw [List.nil_append] at h1
  exact h1

theorem keepF_cons_true {kept rest : List (List α)} {row : List α}
    (h : row.all (fun x => coveredBy cov kept x) = true) : keepF cov kept (row :: rest) = keepF cov kept rest := by
  simp only [keepF, h]

theorem keepF_cons_false {kept rest : List (List α)} {row : List α}
    (h : row.all (fun x => coveredBy cov kept x) = false) :
    keepF cov kept (row :: rest) = keepF cov (kept ++ [row]) rest := by
  simp only [keepF, h]

theorem keepF_sub : ∀ (rest kept : List (List α)) (x : α),
    InLane (keepF cov kept rest) x → InLane (kept ++ rest) x
  | [], kept, x, h => by rw [List.append_nil]; exact h
  | row :: rest, kept, x, h => by
    cases hall : row.all (fun x => coveredBy cov kept x) with
    | true =>
      rw [keepF_cons_true cov hall] at h
      rcases inLane_append.mp (keepF_sub rest kept x h) with h | h
      · exact inLane_append.mpr (Or.inl h)
      · exact inLane_append.mpr (Or.inr (inLane_cons.mpr (Or.inr h)))
    | false =>
      rw [keepF_cons_false cov hall] at h
      have h1 := keepF_sub rest (kept ++ [row]) x h
      rw [List.append_assoc, List.singleton_append] at h1
      exact h1

/-- No new result (landed form). -/
theorem normalizeF_sub (rows : List (List α)) (x : α) :
    InLane (normalizeF cov rows) x → InLane rows x := by
  intro h
  have h1 := keepF_sub cov rows [] x h
  rw [List.nil_append] at h1
  exact h1

theorem coveredBy_of_mem (x y : α) (row : List α) (hyr : y ∈ row) (hyx : cov y x = true) :
    ∀ b : List (List α), row ∈ b → coveredBy cov b x = true
  | [], h => absurd h List.not_mem_nil
  | r :: rs, h => by
    unfold coveredBy
    rw [Bool.or_eq_true]
    rcases List.mem_cons.mp h with h | h
    · subst h; exact Or.inl (List.any_eq_true.mpr ⟨y, hyr, hyx⟩)
    · exact Or.inr (coveredBy_of_mem x y row hyr hyx rs h)

theorem coveredBy_mono (a b : List (List α)) (x : α) (hsub : ∀ y, InLane a y → InLane b y)
    (h : coveredBy cov a x = true) : coveredBy cov b x = true := by
  obtain ⟨y, hy, hyx⟩ := coveredBy_spec cov a x h
  obtain ⟨row, hrow, hyr⟩ := hsub y hy
  exact coveredBy_of_mem cov x y row hyr hyx b hrow

section Cover
variable (hrefl : ∀ x, cov x x = true)
  (htrans : ∀ x y z, cov z y = true → cov y x = true → cov z x = true)
include hrefl

theorem stepWhole_covers (done rest : List (List α)) (row : List α) (x : α)
    (hx : InLane (done ++ row :: rest) x) :
    ∃ y, InLane (done ++ stepWhole cov (done ++ rest) row :: rest) y ∧ cov y x = true := by
  rcases inLane_append.mp hx with h | h
  · exact ⟨x, inLane_append.mpr (Or.inl h), hrefl x⟩
  · rcases inLane_cons.mp h with h | h
    · cases hall : row.all (fun x => coveredBy cov (done ++ rest) x) with
      | true =>
        have hc := List.all_eq_true.mp hall x h
        obtain ⟨y, hy, hcy⟩ := coveredBy_spec cov _ x hc
        refine ⟨y, ?_, hcy⟩
        rcases inLane_append.mp hy with hy | hy
        · exact inLane_append.mpr (Or.inl hy)
        · exact inLane_append.mpr (Or.inr (inLane_cons.mpr (Or.inr hy)))
      | false =>
        refine ⟨x, inLane_append.mpr (Or.inr (inLane_cons.mpr (Or.inl ?_))), hrefl x⟩
        unfold stepWhole
        rw [hall]
        exact h
    · exact ⟨x, inLane_append.mpr (Or.inr (inLane_cons.mpr (Or.inr h))), hrefl x⟩

include htrans in
theorem passW_covers : ∀ (rest done : List (List α)) (x : α), InLane (done ++ rest) x →
    ∃ y, InLane (passW cov done rest) y ∧ cov y x = true
  | [], done, x, h => ⟨x, by rw [List.append_nil] at h; exact h, hrefl x⟩
  | row :: rest, done, x, h => by
    obtain ⟨y, hy, hyx⟩ := stepWhole_covers cov hrefl done rest row x h
    have hy' : InLane ((done ++ [stepWhole cov (done ++ rest) row]) ++ rest) y := by
      rw [List.append_assoc, List.singleton_append]; exact hy
    obtain ⟨z, hz, hzy⟩ := passW_covers rest _ y hy'
    exact ⟨z, hz, htrans x y z hzy hyx⟩

include htrans in
/-- No lost coverage: the normal form covers every coordinate of the replay. -/
theorem normalizeW_covers (rows : List (List α)) (x : α) (hx : InLane rows x) :
    ∃ y, InLane (normalizeW cov rows) y ∧ cov y x = true := by
  have hx' : InLane ([] ++ rows) x := by rw [List.nil_append]; exact hx
  exact passW_covers cov hrefl htrans rows [] x hx'

include htrans in
theorem keepF_covers : ∀ (rest kept : List (List α)) (x : α), InLane (kept ++ rest) x →
    ∃ y, InLane (keepF cov kept rest) y ∧ cov y x = true
  | [], kept, x, h => ⟨x, by rw [List.append_nil] at h; exact h, hrefl x⟩
  | row :: rest, kept, x, h => by
    cases hall : row.all (fun x => coveredBy cov kept x) with
    | true =>
      rw [keepF_cons_true cov hall]
      have key : ∀ z, InLane (kept ++ rest) z → ∃ y, InLane (keepF cov kept rest) y ∧ cov y z = true :=
        fun z hz => keepF_covers rest kept z hz
      rcases inLane_append.mp h with h | h
      · exact key x (inLane_append.mpr (Or.inl h))
      · rcases inLane_cons.mp h with h | h
        · obtain ⟨y, hy, hyx⟩ := coveredBy_spec cov kept x (List.all_eq_true.mp hall x h)
          obtain ⟨z, hz, hzy⟩ := key y (inLane_append.mpr (Or.inl hy))
          exact ⟨z, hz, htrans x y z hzy hyx⟩
        · exact key x (inLane_append.mpr (Or.inr h))
    | false =>
      rw [keepF_cons_false cov hall]
      apply keepF_covers rest (kept ++ [row]) x
      rw [List.append_assoc, List.singleton_append]
      exact h

include htrans in
/-- No lost coverage (landed form): the normal form covers every coordinate of the replay. -/
theorem normalizeF_covers (rows : List (List α)) (x : α) (hx : InLane rows x) :
    ∃ y, InLane (normalizeF cov rows) y ∧ cov y x = true := by
  have hx' : InLane ([] ++ rows) x := by rw [List.nil_append]; exact hx
  exact keepF_covers cov hrefl htrans rows [] x hx'

end Cover

/-- `Good L tail`: no non-empty row of `L` is covered by the other rows of `L` and the rows `tail`. -/
def Good (L tail : List (List α)) : Prop :=
  ∀ A o B, L = A ++ o :: B → o ≠ [] → o.all (fun x => coveredBy cov (A ++ B ++ tail) x) = false

theorem all_coveredBy_mono (a b : List (List α)) (o : List α) (hsub : ∀ y, InLane a y → InLane b y)
    (h : o.all (fun x => coveredBy cov a x) = true) : o.all (fun x => coveredBy cov b x) = true :=
  List.all_eq_true.mpr (fun x hx => coveredBy_mono cov a b x hsub (List.all_eq_true.mp h x hx))

theorem stepWhole_kept (others : List (List α)) (r : List α) (hne : stepWhole cov others r ≠ []) :
    stepWhole cov others r = r ∧ r.all (fun x => coveredBy cov others x) = false := by
  unfold stepWhole at hne ⊢
  cases hall : r.all (fun x => coveredBy cov others x) with
  | true => rw [hall] at hne; exact absurd rfl hne
  | false => exact ⟨rfl, rfl⟩

theorem good_new (done rest : List (List α)) (r : List α) (hne : stepWhole cov (done ++ rest) r ≠ []) :
    (stepWhole cov (done ++ rest) r).all (fun x => coveredBy cov (done ++ rest) x) = false := by
  obtain ⟨heq, hall⟩ := stepWhole_kept cov (done ++ rest) r hne
  rw [heq]
  exact hall

/-- A step keeps `Good`: the new row is not covered (or it is empty), and an older row is now compared
    with a smaller row. -/
theorem good_step (done rest : List (List α)) (r : List α)
    (h : Good cov done (r :: rest)) : Good cov (done ++ [stepWhole cov (done ++ rest) r]) rest := by
  intro A o B hsplit hne
  rcases List.append_eq_append_iff.mp hsplit with ⟨a', hA, hs⟩ | ⟨c', hdone, hs⟩
  · cases a' with
    | nil =>
      rw [List.nil_append] at hs
      injection hs with hso hB
      rw [← hB, ← hso, hA]
      rw [← hso] at hne
      simp only [List.append_nil]
      exact good_new cov done rest r hne
    | cons a as =>
      injection hs with _ hrest
      exact absurd hrest.symm (by simp)
  · cases c' with
    | nil =>
      rw [List.nil_append] at hs
      injection hs with hso hB
      have hA : A = done := by rw [hdone, List.append_nil]
      rw [hB, hso, hA]
      rw [hso] at hne
      simp only [List.append_nil]
      exact good_new cov done rest r hne
    | cons c cs =>
      injection hs with hoc hB
      subst hoc; subst hB
      have hold := h A o cs hdone hne
      cases hc : o.all (fun x => coveredBy cov (A ++ (cs ++ [stepWhole cov (done ++ rest) r]) ++ rest) x) with
      | false => rfl
      | true =>
        have hmono := all_coveredBy_mono cov _ (A ++ cs ++ r :: rest) o (fun y hy => by
          rcases inLane_append.mp hy with hy | hy
          · rcases inLane_append.mp hy with hy | hy
            · exact inLane_append.mpr (Or.inl (inLane_append.mpr (Or.inl hy)))
            · rcases inLane_append.mp hy with hy | hy
              · exact inLane_append.mpr (Or.inl (inLane_append.mpr (Or.inr hy)))
              · obtain ⟨row, hrow, hyr⟩ := hy
                rw [List.mem_singleton] at hrow; subst hrow
                exact inLane_append.mpr (Or.inr (inLane_cons.mpr (Or.inl (stepWhole_sub cov _ r y hyr))))
          · exact inLane_append.mpr (Or.inr (inLane_cons.mpr (Or.inr hy)))) hc
        rw [hold] at hmono
        exact absurd hmono Bool.false_ne_true

theorem passW_good : ∀ (rest done : List (List α)), Good cov done rest → Good cov (passW cov done rest) []
  | [], _, h => h
  | r :: rest, done, h => passW_good rest _ (good_step cov done rest r h)

/-- ONE PASS IS A FIXPOINT: the step at a non-empty row of the normal form, with the other rows of the
    normal form, keeps the row. So a second pass removes nothing. -/
theorem normalizeW_fixpoint (rows : List (List α)) (A B : List (List α)) (o : List α)
    (h : normalizeW cov rows = A ++ o :: B) (hne : o ≠ []) : stepWhole cov (A ++ B) o = o := by
  have hg := passW_good cov rows [] (fun A o B h _ => by simp at h) A o B h hne
  rw [List.append_nil] at hg
  unfold stepWhole
  rw [hg]
  rfl

/-! ## 0'. The statement store -/

theorem sent_sub : ∀ (xs store : List α) (x : α), x ∈ sent cov store xs → x ∈ xs
  | [], _, _, h => absurd h List.not_mem_nil
  | y :: ys, store, x, h => by
    unfold sent at h
    cases hc : coveredIn cov store y with
    | true =>
      rw [hc] at h
      exact List.mem_cons_of_mem _ (sent_sub ys store x h)
    | false =>
      rw [hc] at h
      rcases List.mem_cons.mp h with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons_of_mem _ (sent_sub ys _ x h)

theorem mem_after : ∀ (xs store : List α) (y : α),
    y ∈ after cov store xs ↔ y ∈ sent cov store xs ∨ y ∈ store
  | [], store, y => by
    unfold after sent
    constructor
    · exact Or.inr
    · rintro (h | h)
      · exact absurd h List.not_mem_nil
      · exact h
  | x :: xs, store, y => by
    unfold after sent
    cases hc : coveredIn cov store x with
    | true => exact mem_after xs store y
    | false =>
      show y ∈ after cov (x :: store) xs ↔ y ∈ x :: sent cov (x :: store) xs ∨ y ∈ store
      rw [mem_after xs (x :: store) y]
      constructor
      · rintro (h | h)
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inl (List.mem_cons.mpr (Or.inl h))
          · exact Or.inr h
      · rintro (h | h)
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inr (List.mem_cons.mpr (Or.inl h))
          · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem after_mono (xs store : List α) (y : α) (h : y ∈ store) : y ∈ after cov store xs :=
  (mem_after cov xs store y).mpr (Or.inr h)

theorem sent_cons_true {store xs : List α} {x : α} (h : coveredIn cov store x = true) :
    sent cov store (x :: xs) = sent cov store xs := by
  simp only [sent, h]

theorem sent_cons_false {store xs : List α} {x : α} (h : coveredIn cov store x = false) :
    sent cov store (x :: xs) = x :: sent cov (x :: store) xs := by
  simp only [sent, h]

theorem after_cons_true {store xs : List α} {x : α} (h : coveredIn cov store x = true) :
    after cov store (x :: xs) = after cov store xs := by
  simp only [after, h]

theorem after_cons_false {store xs : List α} {x : α} (h : coveredIn cov store x = false) :
    after cov store (x :: xs) = after cov (x :: store) xs := by
  simp only [after, h]

theorem sent_append : ∀ (xs ys store : List α),
    sent cov store (xs ++ ys) = sent cov store xs ++ sent cov (after cov store xs) ys
  | [], ys, store => rfl
  | x :: xs, ys, store => by
    rw [List.cons_append]
    cases hc : coveredIn cov store x with
    | true =>
      rw [sent_cons_true cov hc, sent_cons_true cov hc, after_cons_true cov hc]
      exact sent_append xs ys store
    | false =>
      rw [sent_cons_false cov hc, sent_cons_false cov hc, after_cons_false cov hc,
        sent_append xs ys (x :: store), List.cons_append]

theorem sent_nil_of_covered : ∀ (ys store : List α),
    (∀ y ∈ ys, coveredIn cov store y = true) → sent cov store ys = []
  | [], _, _ => rfl
  | y :: ys, store, h => by
    unfold sent
    rw [h y List.mem_cons_self]
    exact sent_nil_of_covered ys store (fun z hz => h z (List.mem_cons_of_mem _ hz))

section Cover
variable (hrefl : ∀ x, cov x x = true)
  (htrans : ∀ x y z, cov z y = true → cov y x = true → cov z x = true)
include hrefl

/-- After the arrivals, the sent coordinates cover every arrival. -/
theorem after_covers : ∀ (xs store : List α) (x : α), x ∈ xs →
    ∃ y ∈ after cov store xs, cov y x = true
  | [], _, _, h => absurd h List.not_mem_nil
  | z :: zs, store, x, h => by
    unfold after
    cases hc : coveredIn cov store z with
    | true =>
      show ∃ y ∈ after cov store zs, cov y x = true
      rcases List.mem_cons.mp h with h | h
      · obtain ⟨y, hy, hyz⟩ := (coveredIn_iff cov store z).mp hc
        exact ⟨y, after_mono cov zs store y hy, h ▸ hyz⟩
      · exact after_covers zs store x h
    | false =>
      show ∃ y ∈ after cov (z :: store) zs, cov y x = true
      rcases List.mem_cons.mp h with h | h
      · exact ⟨z, after_mono cov zs (z :: store) z List.mem_cons_self, h ▸ hrefl z⟩
      · exact after_covers zs (z :: store) x h

include htrans

section Normal
/-! Theorems 1 to 4 hold for every normal form that keeps only coordinates of the replay (`nf_sub`)
    and covers every coordinate of the replay (`nf_covers`): the landed form and the order-free form. -/
variable (nf : List (List α) → List (List α))
  (nf_sub : ∀ rows x, InLane (nf rows) x → InLane rows x)
  (nf_covers : ∀ rows x, InLane rows x → ∃ y, InLane (nf rows) y ∧ cov y x = true)

include nf_covers in
/-- The sent coordinates of a batch cover every result of the replay. -/
theorem batch_covers (store : List α) (rows : List (List α)) (x : α) (hx : InLane rows x) :
    ∃ y ∈ after cov store (nf rows).flatten, cov y x = true := by
  obtain ⟨y, hy, hyx⟩ := nf_covers rows x hx
  obtain ⟨z, hz, hzy⟩ := after_covers cov hrefl _ store y (inLane_flatten.mp hy)
  exact ⟨z, hz, htrans x y z hzy hyx⟩

include nf_covers in
/-- THEOREM 1. A batch sends exactly what CURRENT sends when the normal form arrives first. -/
theorem batch_eq_cover_first (store : List α) (rows : List (List α)) :
    batchWith cov nf store rows = sent cov store ((nf rows).flatten ++ rows.flatten) := by
  unfold batchWith
  rw [sent_append, sent_nil_of_covered cov rows.flatten _ ?_, List.append_nil]
  intro x hx
  obtain ⟨z, hz, hzx⟩ := batch_covers cov hrefl htrans nf nf_covers store rows x (inLane_flatten.mpr hx)
  exact (coveredIn_iff cov _ x).mpr ⟨z, hz, hzx⟩

omit hrefl htrans in
include nf_sub in
/-- THEOREM 2. A batch sends only results of the replay. -/
theorem batch_sub (store : List α) (rows : List (List α)) (x : α) (h : x ∈ batchWith cov nf store rows) :
    InLane rows x :=
  nf_sub rows x (inLane_flatten.mpr (sent_sub cov _ store x h))

include nf_sub nf_covers in
/-- THEOREM 3. For every store order of the records, the sent coordinates of CURRENT and of a batch
    cover each other after the replay. -/
theorem batch_equiv_current (store : List α) (rows : List (List α)) :
    (∀ y ∈ after cov store rows.flatten, ∃ z ∈ after cov store (nf rows).flatten, cov z y = true) ∧
    (∀ y ∈ after cov store (nf rows).flatten, ∃ z ∈ after cov store rows.flatten, cov z y = true) := by
  constructor
  · intro y hy
    rcases (mem_after cov _ store y).mp hy with h | h
    · exact batch_covers cov hrefl htrans nf nf_covers store rows y
        (inLane_flatten.mpr (sent_sub cov _ store y h))
    · exact ⟨y, after_mono cov _ store y h, hrefl y⟩
  · intro y hy
    rcases (mem_after cov _ store y).mp hy with h | h
    · have hl : InLane rows y := nf_sub rows y (inLane_flatten.mpr (sent_sub cov _ store y h))
      exact after_covers cov hrefl _ store y (inLane_flatten.mp hl)
    · exact ⟨y, after_mono cov _ store y h, hrefl y⟩

include nf_sub nf_covers in
/-- THEOREM 4. Two replays with the same results (in any order) end with sent coordinates that
    cover each other. -/
theorem batch_perm_equiv (store : List α) (rows rows' : List (List α))
    (hsame : ∀ x, InLane rows x ↔ InLane rows' x) :
    ∀ y ∈ after cov store (nf rows).flatten,
      ∃ z ∈ after cov store (nf rows').flatten, cov z y = true := by
  intro y hy
  rcases (mem_after cov _ store y).mp hy with h | h
  · have hl : InLane rows y := nf_sub rows y (inLane_flatten.mpr (sent_sub cov _ store y h))
    exact batch_covers cov hrefl htrans nf nf_covers store rows' y ((hsame y).mp hl)
  · exact ⟨y, after_mono cov _ store y h, hrefl y⟩

end Normal

/-- THEOREM 1 for the landed form. -/
theorem h2_eq_cover_first (store : List α) (rows : List (List α)) :
    batch cov store rows = sent cov store ((normalizeF cov rows).flatten ++ rows.flatten) :=
  batch_eq_cover_first cov hrefl htrans (normalizeF cov) (normalizeF_covers cov hrefl htrans) store rows

omit hrefl htrans in
/-- THEOREM 2 for the landed form. -/
theorem h2_sub (store : List α) (rows : List (List α)) (x : α) (h : x ∈ batch cov store rows) :
    InLane rows x :=
  batch_sub cov (normalizeF cov) (normalizeF_sub cov) store rows x h

/-- THEOREM 3 for the landed form. -/
theorem h2_equiv_current (store : List α) (rows : List (List α)) :
    (∀ y ∈ after cov store rows.flatten,
      ∃ z ∈ after cov store (normalizeF cov rows).flatten, cov z y = true) ∧
    (∀ y ∈ after cov store (normalizeF cov rows).flatten,
      ∃ z ∈ after cov store rows.flatten, cov z y = true) :=
  batch_equiv_current cov hrefl htrans (normalizeF cov) (normalizeF_sub cov)
    (normalizeF_covers cov hrefl htrans) store rows

/-- THEOREM 4 for the landed form. -/
theorem h2_perm_equiv (store : List α) (rows rows' : List (List α))
    (hsame : ∀ x, InLane rows x ↔ InLane rows' x) :
    ∀ y ∈ after cov store (normalizeF cov rows).flatten,
      ∃ z ∈ after cov store (normalizeF cov rows').flatten, cov z y = true :=
  batch_perm_equiv cov hrefl htrans (normalizeF cov) (normalizeF_sub cov)
    (normalizeF_covers cov hrefl htrans) store rows rows' hsame

/-- THEOREM 1 for the order-free form (v2). -/
theorem h2w_eq_cover_first (store : List α) (rows : List (List α)) :
    batchW cov store rows = sent cov store ((normalizeW cov rows).flatten ++ rows.flatten) :=
  batch_eq_cover_first cov hrefl htrans (normalizeW cov) (normalizeW_covers cov hrefl htrans) store rows

end Cover
end Generic

/-! ## Vectors: the Stirling-PDF lane at `attachment.getFilename()` (checked by `decide`) -/

namespace Vec
/-- A coordinate: a path below `ret` and the tail bit (`true` = MUST, an `[any-taint]` leaf with an
    empty exclusion: it covers itself and every coordinate below its path). -/
abbrev Coord := List Nat × Bool
def vcov (y x : Coord) : Bool :=
  (y == x) || (y.2 && y.1.isPrefixOf x.1)
/-- R_s: `<this>.filename.*/FLOW -> {ret.*/FLOW}` gives `ret.MUST/xss`. -/
def rs : List Coord := [([], true)]
/-- R_d: `<this>.filename.MUST/FLOW -> {ret.[] | Matcher#group | Matcher#input | String#bytes}.MUST`
    (accessors 1 to 4). -/
def rd : List Coord := [([1], true), ([2], true), ([3], true), ([4], true)]
/-- The general-first order of production (the shallowest leaf first; stable), as an insertion sort. -/
def minDepth (row : List Coord) : Nat := row.foldl (fun m c => min m c.1.length) 1000
def ins (r : List Coord) : List (List Coord) → List (List Coord)
  | [] => [r]
  | s :: ss => if minDepth r ≤ minDepth s then r :: s :: ss else s :: ins r ss
def isort : List (List Coord) → List (List Coord)
  | [] => []
  | r :: rs => ins r (isort rs)
/-- CURRENT, the deep record first (costly sub-form): the deep results go on. -/
example : current vcov [] [rd, rs] = [([1], true), ([2], true), ([3], true), ([4], true), ([], true)] := by decide
/-- CURRENT, the cover first (cheap sub-form): only the cover goes on. -/
example : current vcov [] [rs, rd] = [([], true)] := by decide
/-- H2 (landed form, general-first order): only the cover goes on, in both store orders. -/
example : batch vcov [] (isort [rd, rs]) = [([], true)] := by decide
example : batch vcov [] (isort [rs, rd]) = [([], true)] := by decide
/-- Without the general-first order, one store in the store order is CURRENT again: the order is
    part of the rule. -/
example : batch vcov [] [rd, rs] = [([1], true), ([2], true), ([3], true), ([4], true), ([], true)] := by decide
/-- The order-free form (v2) gives only the cover in both orders, without a sort. -/
example : batchW vcov [] [rd, rs] = [([], true)] := by decide
example : batchW vcov [] [rs, rd] = [([], true)] := by decide
/-- The second site (`content.getHtmlBody()`): `CharSequence#content` (5) and `String#bytes` (4). -/
def rd2 : List Coord := [([5], true), ([4], true)]
example : current vcov [] [rd2, rs] = [([5], true), ([4], true), ([], true)] := by decide
example : batch vcov [] (isort [rd2, rs]) = [([], true)] := by decide
/-- A result that the cover does not cover stays (another base path is not below `ret`; here an
    exact coordinate next to a MUST coordinate at another path). -/
def other : List Coord := [([7], false)]
example : batch vcov [] (isort [other, rd]) =
    [([7], false), ([1], true), ([2], true), ([3], true), ([4], true)] := by decide
end Vec

end ApSpec.ReplayBatch

#print axioms ApSpec.ReplayBatch.sent_sub
#print axioms ApSpec.ReplayBatch.mem_after
#print axioms ApSpec.ReplayBatch.sent_append
#print axioms ApSpec.ReplayBatch.after_covers
#print axioms ApSpec.ReplayBatch.batch_covers
#print axioms ApSpec.ReplayBatch.batch_eq_cover_first
#print axioms ApSpec.ReplayBatch.batch_sub
#print axioms ApSpec.ReplayBatch.batch_equiv_current
#print axioms ApSpec.ReplayBatch.batch_perm_equiv
#print axioms ApSpec.ReplayBatch.keepF_sub
#print axioms ApSpec.ReplayBatch.keepF_covers
#print axioms ApSpec.ReplayBatch.h2_eq_cover_first
#print axioms ApSpec.ReplayBatch.h2_sub
#print axioms ApSpec.ReplayBatch.h2_equiv_current
#print axioms ApSpec.ReplayBatch.h2_perm_equiv
#print axioms ApSpec.ReplayBatch.h2w_eq_cover_first
#print axioms ApSpec.ReplayBatch.normalizeW_sub
#print axioms ApSpec.ReplayBatch.normalizeW_covers
#print axioms ApSpec.ReplayBatch.coveredBy_mono
#print axioms ApSpec.ReplayBatch.good_step
#print axioms ApSpec.ReplayBatch.normalizeW_fixpoint
