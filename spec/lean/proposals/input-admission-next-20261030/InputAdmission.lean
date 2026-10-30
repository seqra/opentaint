import Std

/-!
A proposal model only. Coordinates include the full path, exact/any leaf kind,
and full mark. Root operations are literal coordinate operations, not AP cover.
The common header and its canonicalizer do not change in this optimization.
-/
namespace InputAdmission

abbrev Root (n : Nat) := Fin n → Bool
def empty : Root n := fun _ => false
def included (p r : Root n) : Prop := ∀ c, p c = true → r c = true
def union (a b : Root n) : Root n := fun c => a c || b c
def difference (a b : Root n) : Root n := fun c => a c && !b c
def trim (p r : Root n) : Root n := fun c => p c && r c
def isEmpty (r : Root n) : Bool := (List.finRange n).all fun c => !r c

theorem isEmpty_exact (r : Root n) : isEmpty r = true ↔ r = empty := by
  constructor
  · intro h
    funext c
    have hc := List.all_eq_true.mp h c (List.mem_finRange c)
    cases hr : r c <;> simp_all [empty]
  · intro h
    subst r
    simp [isEmpty, empty]

theorem trim_identity (p r : Root n) (h : included p r) : trim p r = p := by
  funext c
  cases hp : p c with
  | false => simp [trim, hp]
  | true => simp [trim, hp, h c hp]

theorem union_included (p0 p1 r0 r1 : Root n)
    (h0 : included p0 r0) (h1 : included p1 r1) :
    included (union p0 p1) (union r0 r1) := by
  intro c h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · simp [union, h0 c h]
  · simp [union, h1 c h]

theorem difference_subset (a b : Root n) : included (difference a b) a := by
  intro c h
  exact (Bool.and_eq_true_iff.mp h).1

theorem right_in_union (a b : Root n) : included b (union a b) := by
  intro c h
  simp [union, h]

theorem difference_self (a : Root n) : difference a a = empty := by
  funext c
  cases h : a c <;> simp [difference, empty, h]

theorem union_same (a : Root n) : union a a = a := by
  funext c
  cases h : a c <;> simp [union, h]

theorem union_unchanged_of_no_difference (old offered : Root n)
    (h : difference offered old = empty) : union old offered = old := by
  funext c
  have hc := congrFun h c
  cases ho : old c <;> cases hn : offered c <;>
    simp_all [difference, empty, union]

theorem empty_union (a b : Root n) :
    union a b = empty ↔ a = empty ∧ b = empty := by
  constructor
  · intro h
    constructor
    · funext c
      have hc := congrFun h c
      cases ha : a c <;> cases hb : b c <;> simp_all [union, empty]
    · funext c
      have hc := congrFun h c
      cases ha : a c <;> cases hb : b c <;> simp_all [union, empty]
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Existing ordinary mergeAddDelta has this exact coordinate delta. -/
def ordinaryDelta (r0 r1 : Root n) : Root n := difference r1 r0
/-- Existing annotationDelta uses literal minusNode, not AP coverage. -/
def annotationDelta (p0 p1 : Root n) : Root n := difference p1 p0
def emittedRoot (r0 r1 p0 p1 : Root n) : Root n :=
  union (ordinaryDelta r0 r1) (annotationDelta p0 p1)

/-- No old protected coordinate can occur in a fresh ordinary delta. -/
theorem old_mask_disjoint_ordinary_delta (p0 r0 r1 : Root n)
    (h0 : included p0 r0) : trim p0 (ordinaryDelta r0 r1) = empty := by
  funext c
  have hc := h0 c
  cases hp : p0 c <;> cases ho : r0 c <;> cases hn : r1 c <;>
    simp_all [trim, ordinaryDelta, difference, empty]

/-- The exact delta mask is already computed by the baseline algorithm. -/
theorem delta_mask_exact (p0 p1 r0 r1 : Root n)
    (h0 : included p0 r0) (h1 : included p1 r1) :
    trim (union p0 p1) (emittedRoot r0 r1 p0 p1) = annotationDelta p0 p1 := by
  funext c
  have h0c := h0 c
  have h1c := h1 c
  cases hpa : p0 c <;> cases hpb : p1 c <;>
    cases hra : r0 c <;> cases hrb : r1 c <;>
    simp_all [trim, union, emittedRoot, ordinaryDelta, annotationDelta, difference]

theorem delta_mask_included (p0 p1 r0 r1 : Root n) :
    included (annotationDelta p0 p1) (emittedRoot r0 r1 p0 p1) :=
  right_in_union _ _

theorem delta_empty_exact (p0 p1 r0 r1 : Root n) :
    emittedRoot r0 r1 p0 p1 = empty ↔
      ordinaryDelta r0 r1 = empty ∧ annotationDelta p0 p1 = empty :=
  empty_union _ _

structure Tree (Header : Type) (n : Nat) where
  header : Header
  ordinary : Root n
  mask : Root n

def normalized {H : Type} (canonical : H → Root n → H) (t : Tree H n) : Prop :=
  canonical t.header t.ordinary = t.header

def legacyTree {H : Type} (canonical : H → Root n → H)
    (header : H) (r p : Root n) : Tree H n :=
  ⟨canonical header r, r, trim p r⟩

def admittedTree {H : Type} (canonical : H → Root n → H)
    (header : H) (r p : Root n) : Tree H n :=
  ⟨canonical header r, r, p⟩

theorem stored_constructor_exact {H : Type} (canonical : H → Root n → H)
    (header : H) (p0 p1 r0 r1 : Root n)
    (h0 : included p0 r0) (h1 : included p1 r1) :
    legacyTree canonical header (union r0 r1) (union p0 p1) =
      admittedTree canonical header (union r0 r1) (union p0 p1) := by
  simp [legacyTree, admittedTree, trim_identity _ _ (union_included _ _ _ _ h0 h1)]

theorem delta_constructor_exact {H : Type} (canonical : H → Root n → H)
    (header : H) (p0 p1 r0 r1 : Root n)
    (h0 : included p0 r0) (h1 : included p1 r1) :
    legacyTree canonical header (emittedRoot r0 r1 p0 p1) (union p0 p1) =
      admittedTree canonical header (emittedRoot r0 r1 p0 p1) (annotationDelta p0 p1) := by
  simp [legacyTree, admittedTree, delta_mask_exact _ _ _ _ h0 h1]

/-- The baseline constructs the stored tree even when its returned delta is absent. -/
def legacyMerge {H : Type} (canonical : H → Root n → H)
    (old offered : Tree H n) : Tree H n × Option (Tree H n) :=
  let p := union old.mask offered.mask
  let d := emittedRoot old.ordinary offered.ordinary old.mask offered.mask
  (legacyTree canonical old.header (union old.ordinary offered.ordinary) p,
   if isEmpty d then none else some (legacyTree canonical old.header d p))

/-- Decide delta emptiness before merged-mask or merged-tree construction. -/
def newMerge {H : Type} (canonical : H → Root n → H)
    (old offered : Tree H n) : Tree H n × Option (Tree H n) :=
  let d := ordinaryDelta old.ordinary offered.ordinary
  let dp := annotationDelta old.mask offered.mask
  if isEmpty d && isEmpty dp then (old, none) else
    (admittedTree canonical old.header (union old.ordinary offered.ordinary)
       (union old.mask offered.mask),
     if isEmpty (union d dp) then none else
       some (admittedTree canonical old.header (union d dp) dp))

theorem noop_state_and_delta {H : Type} (canonical : H → Root n → H)
    (old offered : Tree H n) (h0 : included old.mask old.ordinary)
    (hn : normalized canonical old)
    (hd : ordinaryDelta old.ordinary offered.ordinary = empty)
    (hp : annotationDelta old.mask offered.mask = empty) :
    legacyMerge canonical old offered = (old, none) := by
  have hr := union_unchanged_of_no_difference old.ordinary offered.ordinary hd
  have hm := union_unchanged_of_no_difference old.mask offered.mask hp
  have he : emittedRoot old.ordinary offered.ordinary old.mask offered.mask = empty :=
    (delta_empty_exact _ _ _ _).2 ⟨hd, hp⟩
  have hh := hn
  unfold normalized at hh
  simp [legacyMerge, hr, hm, he, isEmpty_exact, legacyTree, trim_identity _ _ h0, hh]

theorem merge_state_and_delta_exact {H : Type} (canonical : H → Root n → H)
    (old offered : Tree H n) (_sameHeader : old.header = offered.header)
    (h0 : included old.mask old.ordinary) (h1 : included offered.mask offered.ordinary)
    (hn : normalized canonical old) :
    legacyMerge canonical old offered = newMerge canonical old offered := by
  unfold newMerge
  dsimp only
  split
  · rename_i h
    obtain ⟨hd, hp⟩ := Bool.and_eq_true_iff.mp h
    exact noop_state_and_delta canonical old offered h0 hn
      ((isEmpty_exact _).1 hd) ((isEmpty_exact _).1 hp)
  · unfold legacyMerge
    dsimp only
    change (legacyTree canonical old.header (union old.ordinary offered.ordinary) (union old.mask offered.mask),
      if isEmpty (emittedRoot old.ordinary offered.ordinary old.mask offered.mask) then none else
        some (legacyTree canonical old.header (emittedRoot old.ordinary offered.ordinary old.mask offered.mask)
          (union old.mask offered.mask))) =
      (admittedTree canonical old.header (union old.ordinary offered.ordinary) (union old.mask offered.mask),
       if isEmpty (emittedRoot old.ordinary offered.ordinary old.mask offered.mask) then none else
         some (admittedTree canonical old.header (emittedRoot old.ordinary offered.ordinary old.mask offered.mask)
           (annotationDelta old.mask offered.mask)))
    rw [stored_constructor_exact canonical old.header old.mask offered.mask
      old.ordinary offered.ordinary h0 h1]
    split
    · rfl
    · rw [delta_constructor_exact canonical old.header old.mask offered.mask
        old.ordinary offered.ordinary h0 h1]

/-- Header-only metadata is the same constructor input on both nonempty outputs. -/
theorem constructor_header_unchanged {H : Type} (canonical : H → Root n → H)
    (header : H) (r p q : Root n) :
    (legacyTree canonical header r p).header =
      (admittedTree canonical header r q).header := rfl

/-- Count constructor normalization calls, not visited nodes or elapsed time. -/
def legacyTrimCalls (r0 r1 p0 p1 : Root n) : Nat :=
  if isEmpty (union p0 p1) then 0 else
    1 + if isEmpty (emittedRoot r0 r1 p0 p1) then 0 else 1

def newTrimCalls (_r0 _r1 _p0 _p1 : Root n) : Nat := 0

theorem no_new_normalization_calls (r0 r1 p0 p1 : Root n) :
    newTrimCalls r0 r1 p0 p1 = 0 := rfl

theorem protected_normalization_calls_removed (r0 r1 p0 p1 : Root n)
    (h : isEmpty (union p0 p1) = false) :
    newTrimCalls r0 r1 p0 p1 < legacyTrimCalls r0 r1 p0 p1 := by
  simp only [newTrimCalls, legacyTrimCalls, h, Bool.false_eq_true, ↓reduceIte]
  split <;> decide

def newTreeConstructions (r0 r1 p0 p1 : Root n) : Nat :=
  if isEmpty (ordinaryDelta r0 r1) && isEmpty (annotationDelta p0 p1) then 0 else
    1 + if isEmpty (emittedRoot r0 r1 p0 p1) then 0 else 1

theorem noop_constructs_no_tree (r0 r1 p0 p1 : Root n)
    (hd : ordinaryDelta r0 r1 = empty) (hp : annotationDelta p0 p1 = empty) :
    newTreeConstructions r0 r1 p0 p1 = 0 := by
  simp [newTreeConstructions, hd, hp, isEmpty_exact]

/-- Fresh ordinary coordinates plus annotation upgrades still cover the offered input. -/
theorem old_and_delta_cover_union (p0 p1 r0 r1 : Root n)
    (h1 : included p1 r1) :
    union r0 (emittedRoot r0 r1 p0 p1) = union r0 r1 := by
  funext c
  have h1c := h1 c
  cases hpa : p0 c <;> cases hpb : p1 c <;>
    cases hra : r0 c <;> cases hrb : r1 c <;>
    simp_all [union, emittedRoot, ordinaryDelta, annotationDelta, difference]

/-- A finite leafwise transfer; each input coordinate has an executable output root. -/
def imageRows (rows : List (Fin n)) (emit : Fin n → Root k) (r : Root n) : Root k :=
  match rows with
  | [] => empty
  | c :: rest => if r c then union (emit c) (imageRows rest emit r) else imageRows rest emit r

def image (emit : Fin n → Root k) (r : Root n) : Root k :=
  imageRows (List.finRange n) emit r

theorem image_rows_distributes (rows : List (Fin n)) (emit : Fin n → Root k)
    (a b : Root n) :
    imageRows rows emit (union a b) = union (imageRows rows emit a) (imageRows rows emit b) := by
  induction rows with
  | nil => rfl
  | cons c rest ih =>
    funext d
    cases ha : a c <;> cases hb : b c <;>
      simp [imageRows, union, ha, hb, ih, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

theorem image_distributes (emit : Fin n → Root k) (a b : Root n) :
    image emit (union a b) = union (image emit a) (image emit b) :=
  image_rows_distributes _ _ _ _

/-- Cumulative leafwise initial emission is unchanged when only fresh input is linked. -/
theorem fresh_link_observations_exact (emit : Fin n → Root k)
    (p0 p1 r0 r1 : Root n) (h1 : included p1 r1) :
    union (image emit r0) (image emit (emittedRoot r0 r1 p0 p1)) =
      image emit (union r0 r1) := by
  rw [← image_distributes]
  rw [old_and_delta_cover_union _ _ _ _ h1]

/-- General mask trimming is retained outside the two proved merge constructors. -/
theorem general_trim_remains (p r : Root n) : included (trim p r) r := by
  intro c h
  exact (Bool.and_eq_true_iff.mp h).2

def a : Root 2 := fun c => c.val == 0
def b : Root 2 := fun c => c.val == 1

theorem merged_mask_must_not_be_reused_for_delta : ¬ included a b := by
  intro h
  have impossible := h 0 (by decide)
  contradiction

theorem fresh_plain_coordinate_has_no_delta_mask :
    trim (union a a) (emittedRoot a (union a b) a a) = empty := by
  have ha : included a a := fun _ h => h
  have hab : included a (union a b) := by intro c h; simp [union, h]
  rw [delta_mask_exact a a a (union a b) ha hab]
  exact difference_self _

/-- Executable witnesses return both roots; no classical existence is used. -/
def oldExample : Tree Unit 2 := ⟨(), a, a⟩
def plainGrowth : Tree Unit 2 := ⟨(), union a b, a⟩
def protectionGrowth : Tree Unit 2 := ⟨(), union a b, union a b⟩
def alreadyOrdinary : Tree Unit 2 := ⟨(), union a b, a⟩
def identityHeader (h : Unit) (_ : Root 2) : Unit := h

#guard (newMerge identityHeader oldExample oldExample).2.isNone
#guard match (newMerge identityHeader oldExample plainGrowth).2 with
  | none => false
  | some t => t.ordinary 1 && !t.ordinary 0 && isEmpty t.mask
#guard match (newMerge identityHeader oldExample protectionGrowth).2 with
  | none => false
  | some t => t.ordinary 1 && t.mask 1 && !t.mask 0
#guard match (newMerge identityHeader alreadyOrdinary protectionGrowth).2 with
  | none => false
  | some t => t.ordinary 1 && t.mask 1 && !t.mask 0
#guard isEmpty (ordinaryDelta alreadyOrdinary.ordinary protectionGrowth.ordinary)
#guard (newMerge identityHeader protectionGrowth oldExample).2.isNone
#guard !isEmpty (ordinaryDelta a (union a b))
#guard isEmpty (annotationDelta a a)
#guard !isEmpty (annotationDelta empty a)

end InputAdmission
