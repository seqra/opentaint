import ScopedCore
import HeadDeep
import HeadShallow
import HeadAlternating
namespace ScopedHomogeneous
open NonEmptyPolicy NonEmptyRestriction AlternatingCondition
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

theorem old_generator_has_one_output_mark (m : Color) (q : Seed) :
    (CompletePoint.gen m q).all (fun c => c.ap.mark==some m.flip.id)=true := by
  unfold CompletePoint.gen
  split
  · rfl
  · simp only [List.all_append,Bool.and_eq_true]
    constructor
    · split
      · simp [value,fact]
      · cases found : dropHead q.ap.path [f,g,g] with
        | none => simp [found]
        | some path =>
          cases path with
          | nil => simp [found]
          | cons field rest =>
            simp only [found]
            split <;> simp [value,fact]
    · simp [value,fact]

-- A nonempty generator output also fixes the input mark.
theorem output_requires_input_mark (m : Color) (q : Seed) (c : Value)
    (member : c ∈ CompletePoint.gen m q) : q.ap.mark=some m.id := by
  by_cases same : q.ap.mark=some m.id
  · exact same
  · have empty : CompletePoint.gen m q=[] := by simp [CompletePoint.gen,same]
    rw [empty] at member
    cases member

theorem old_raw_returns_are_homogeneous (q : Seed) :
    ∀ c ∈ CompletePoint.colors.flatMap (fun m => CompletePoint.gen m q),
      c.ap.mark=some (if q.ap.mark==some 1 then 2 else 1) := by
  intro c hc
  rcases List.mem_flatMap.mp hc with ⟨m,_,member⟩
  have color := List.all_eq_true.mp (old_generator_has_one_output_mark m q) c member
  have input := output_requires_input_mark m q c member
  cases m <;> simpa [input,Color.id,Color.flip] using color

theorem old_exact_case_gets_no_new_scoped_cells (current : List ScopedCore.Edge) (q : Seed) :
    ScopedCore.extra current q (CompletePoint.colors.flatMap fun m => CompletePoint.gen m q)=[] :=
  ScopedCore.homogeneous_query_gets_no_extra_cells current q _ _ (old_raw_returns_are_homogeneous q)

theorem deep_real_E_body_is_the_same_generator (m : Color) (q : Seed) :
    HeadDeep.gen m q=CompletePoint.gen m q := rfl

theorem shallow_generator_has_one_output_mark (m : Color) (q : Seed) :
    (HeadShallow.gen m q).all (fun c => c.ap.mark==some m.flip.id)=true := by
  unfold HeadShallow.gen
  split
  · rfl
  · simp only [List.all_append,Bool.and_eq_true]
    constructor
    · split
      · simp [value,fact]
      · cases found : dropHead q.ap.path [f,g] with
        | none => simp [found]
        | some path =>
          cases path with
          | nil => simp [found]
          | cons field rest =>
            simp only [found]
            split <;> simp [value,fact]
    · simp [value,fact]

theorem alternating_generator_has_one_output_mark (m : Color) (q : Seed) :
    (generate m q).all (fun c => c.ap.mark==some m.flip.id)=true := by
  unfold generate
  split
  · rfl
  · simp only [List.all_append,Bool.and_eq_true]
    constructor
    · split
      · simp [value,fact]
      · split <;> simp [value,fact]
    · simp [value,fact]

theorem shallow_output_requires_input_mark (m : Color) (q : Seed) (c : Value)
    (member : c ∈ HeadShallow.gen m q) : q.ap.mark=some m.id := by
  by_cases same : q.ap.mark=some m.id
  · exact same
  · have empty : HeadShallow.gen m q=[] := by simp [HeadShallow.gen,same]
    rw [empty] at member
    cases member

theorem alternating_output_requires_input_mark (m : Color) (q : Seed) (c : Value)
    (member : c ∈ generate m q) : q.ap.mark=some m.id := by
  by_cases same : q.ap.mark=some m.id
  · exact same
  · have empty : generate m q=[] := by simp [generate,same]
    rw [empty] at member
    cases member

theorem homogeneous_colored_family (G : Color → Seed → List Value)
    (input : ∀ m q c,c ∈ G m q → q.ap.mark=some m.id)
    (output : ∀ m q,(G m q).all (fun c => c.ap.mark==some m.flip.id)=true)
    (q : Seed) : ∀ c ∈ [.t,.u].flatMap (fun m => G m q),
      c.ap.mark=some (if q.ap.mark==some 1 then 2 else 1) := by
  intro c hc
  rcases List.mem_flatMap.mp hc with ⟨m,_,member⟩
  have color := List.all_eq_true.mp (output m q) c member
  have cameFrom := input m q c member
  cases m <;> simpa [cameFrom,Color.id,Color.flip] using color

theorem old_shallow_case_gets_no_new_scoped_cells (current : List ScopedCore.Edge) (q : Seed) :
    ScopedCore.extra current q ([.t,.u].flatMap fun m => HeadShallow.gen m q)=[] :=
  ScopedCore.homogeneous_query_gets_no_extra_cells current q _ _
    (homogeneous_colored_family HeadShallow.gen shallow_output_requires_input_mark
      shallow_generator_has_one_output_mark q)

theorem old_alternating_case_gets_no_new_scoped_cells (current : List ScopedCore.Edge) (q : Seed) :
    ScopedCore.extra current q ([.t,.u].flatMap fun m => generate m q)=[] :=
  ScopedCore.homogeneous_query_gets_no_extra_cells current q _ _
    (homogeneous_colored_family generate alternating_output_requires_input_mark
      alternating_generator_has_one_output_mark q)

theorem abstract_queries_get_no_new_scoped_cells (current : List ScopedCore.Edge)
    (q : Seed) (raw : List Value) (flow : q.ap.mark=none) : ScopedCore.extra current q raw=[] := by
  have notEligible : ScopedCore.eligible q=false := by simp [ScopedCore.eligible,flow]
  have failed (m : Nat) : ScopedCore.completeFor current q raw m=false := by
    simp only [ScopedCore.completeFor,notEligible,Bool.false_and]
  unfold ScopedCore.extra ScopedCore.whole
  simp only [notEligible,Bool.false_and,Bool.false_eq_true,ite_false]
  generalize ScopedCore.existingMarks current q = marks
  induction marks with
  | nil => rfl
  | cons mark rest ih => simp only [List.filter_cons,failed mark,Bool.false_eq_true,ite_false,ih]

end ScopedHomogeneous
