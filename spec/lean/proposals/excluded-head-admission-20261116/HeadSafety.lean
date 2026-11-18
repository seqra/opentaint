import HeadPolicy
import CarrySafety
namespace HeadSafety
open NonEmptyPolicy NonEmptyRestriction HeadPolicy
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

theorem preserves_kind_mark_support (a : Offered) (q : Seed) :
    (retain a q).ap.base=q.ap.base ∧ (retain a q).ap.tail=q.ap.tail ∧
    (retain a q).ap.mark=q.ap.mark ∧ (retain a q).ap.mx=q.ap.mx ∧
    (retain a q).demand=q.demand := by
  unfold retain; split <;> simp

theorem path_and_E_are_one_existing_pair (a : Offered) (q : Seed) :
    ((retain a q).ap.path=q.ap.path ∧ (retain a q).ap.e=q.ap.e) ∨
    ((retain a q).ap.path=a.ap.path ∧ (retain a q).ap.e=a.ap.e) := by
  unfold retain; split <;> simp

theorem retains_the_actual_point_region (a : Offered) (q : Seed)
    (yes : eligible a q=true) (location : Path) :
    UniformActual.locationIn (retain a q).ap location ↔
    UniformActual.locationIn a.ap location := by
  have shape := yes
  unfold eligible at shape
  simp only [Bool.and_eq_true] at shape
  have qt : q.ap.tail=.star := by cases t:q.ap.tail <;> simp_all
  cases atail:a.ap.tail <;>
    simp_all [retain,eligible,UniformActual.locationIn,admits]
  constructor
  · rintro ⟨rest,whereAt,allowed⟩
    refine ⟨rest,whereAt,?_⟩
    cases rest with
    | nil => rfl
    | cons f rest => exact allowed
  · rintro ⟨rest,whereAt,allowed⟩
    refine ⟨rest,whereAt,?_⟩
    cases rest with
    | nil => rfl
    | cons f rest => exact allowed

theorem already_excluded_initial_is_unchanged (a : Offered) (q : Seed)
    (h : q.ap.e.isEmpty=false) : retain a q=q := by simp [retain,eligible,h]

theorem no_uniform_initial_is_split (a : Offered) (q : Seed)
    (h : q.ap.tail=.must) : retain a q=q := by simp [retain,eligible,h]

theorem no_point_probe_is_changed (a : Offered) (q : Seed)
    (h : q.ap.tail=.exact) : retain a q=q := by simp [retain,eligible,h]

theorem exact_old_family_size (run k : Nat) (back : Bool) (d : Ap) (a : Offered) :
    (HeadPolicy.emit run k back d a).length=(CarryPolicy.emit run k back d a).length := by
  unfold HeadPolicy.emit; split <;> simp

theorem every_new_start_has_an_executable_old_witness
    (run k : Nat) (back : Bool) (d : Ap) (a : Offered) (q : Seed)
    (hq : q ∈ HeadPolicy.emit run k back d a) :
    ∃ old ∈ CarryPolicy.emit run k back d a, q=old ∨ q=retain a old := by
  unfold HeadPolicy.emit at hq
  split at hq
  · exact ⟨q,hq,Or.inl rfl⟩
  · rcases List.mem_map.mp hq with ⟨old,inside,same⟩
    exact ⟨old,inside,Or.inr same.symm⟩

theorem too_deep_actual_has_no_old_family (run k : Nat) (back : Bool)
    (d : Ap) (a : Offered) (deep : k<a.ap.path.length) :
    CarryPolicy.emit run k back d a=[] := by
  simp [CarryPolicy.emit,NonEmptyPolicy.emit,emitBase,deep]

theorem actual_bound_from_old_admission (run k : Nat) (back : Bool)
    (d : Ap) (a : Offered) (q : Seed) (inside : q ∈ CarryPolicy.emit run k back d a) :
    a.ap.path.length ≤ k := by
  by_cases h : k<a.ap.path.length
  · rw [too_deep_actual_has_no_old_family run k back d a h] at inside
    cases inside
  · omega

theorem every_new_start_stays_globally_bounded (run k : Nat) (back : Bool)
    (d : Ap) (a : Offered) (q : Seed) (inside : q ∈ HeadPolicy.emit run k back d a) :
    q.ap.path.length ≤ k := by
  rcases every_new_start_has_an_executable_old_witness run k back d a q inside with ⟨old,oldIn,same⟩
  rcases same with same | same
  · rw [same]
    exact (CarrySafety.emitted_legal run k back d a old oldIn).1
  · rw [same]
    rcases path_and_E_are_one_existing_pair a old with original | actual
    · rw [original.1]
      exact (CarrySafety.emitted_legal run k back d a old oldIn).1
    · rw [actual.1]
      exact actual_bound_from_old_admission run k back d a old oldIn

theorem never_owned_MAY_or_NE (run k : Nat) (back : Bool) (d : Ap) (a : Offered)
    (q : Seed) (inside : q ∈ HeadPolicy.emit run k back d a) :
    q.ap.tail≠.may ∧ q.ap.tail≠.ne := by
  rcases every_new_start_has_an_executable_old_witness run k back d a q inside with ⟨old,oldIn,same⟩
  have legal := CarrySafety.no_owned_may_or_ne run k back d a old oldIn
  rcases same with same | same
  · simpa [same] using legal
  · rw [same]
    simpa only [(preserves_kind_mark_support a old).2.1] using legal

theorem raw_C5_has_a_constructive_offer (run k : Nat) (back : Bool) (d : Ap)
    (as : List Offered) (raw : Ap) (inside : raw ∈ HeadPolicy.rawImage run k back d as) :
    ∃ a ∈ as, ∃ q ∈ HeadPolicy.emit run k back d a, q.ap=raw := by
  rcases List.mem_flatMap.mp inside with ⟨a,offered,inMap⟩
  rcases List.mem_map.mp inMap with ⟨q,emitted,same⟩
  exact ⟨a,offered,q,emitted,same⟩

theorem flatMap_congr {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ x ∈ xs, f x=g x) : xs.flatMap f=xs.flatMap g := by
  exact CarrySafety.flatMap_congr xs f g h

theorem empty_members (as : List Offered)
    (yes : as.all (fun a => a.ap.e.isEmpty)=true) : ∀ a ∈ as, a.ap.e=[] := by
  exact CarrySafety.empty_members as yes

theorem empty_actuals_C5_matches_carried_policy (run k : Nat) (back : Bool)
    (as : List Offered) (raw : Ap) (c : Value) (row : Row)
    (empty : ∀ a ∈ as, a.ap.e=[]) :
    HeadPolicy.restrictOne run k back as raw c row=
      CarryPolicy.restrictOne run k back as raw c row := by
  have image : HeadPolicy.rawImage run k back row.entry as=CarryPolicy.rawImage run k back row.entry as := by
    unfold HeadPolicy.rawImage CarryPolicy.rawImage
    apply flatMap_congr
    intro a inside
    rw [HeadPolicy.empty_E_unchanged run k back row.entry a (empty a inside)]
  simp only [HeadPolicy.restrictOne,CarryPolicy.restrictOne,image]

theorem empty_actuals_C5_is_unchanged (run k : Nat) (back : Bool)
    (as : List Offered) (raw : Ap) (c : Value) (row : Row)
    (empty : ∀ a ∈ as, a.ap.e=[]) :
    HeadPolicy.restrictOne run k back as raw c row=
      NonEmptyRestriction.restrictOne run k back as raw c row := by
  rw [empty_actuals_C5_matches_carried_policy run k back as raw c row empty]
  exact CarrySafety.empty_actuals_C5_is_unchanged run k back as raw c row empty

theorem no_query_after_old_rejection (run k : Nat) (back : Bool) (d : Ap) (a : Offered)
    (empty : CarryPolicy.emit run k back d a=[]) : HeadPolicy.emit run k back d a=[] := by
  simp [HeadPolicy.emit,empty]

theorem precise_selectors_are_not_relaxed (run k : Nat) (back : Bool)
    (d : Ap) (a : Offered) (notMay : d.tail≠.may) (notNE : d.tail≠.ne) :
    HeadPolicy.emit run k back d a=CarryPolicy.emit run k back d a := by
  simp [HeadPolicy.emit,notMay,notNE]

theorem every_real_excluded_descendant_is_still_excluded
    (a : Offered) (q : Seed) (yes : eligible a q=true) (f : Nat) (rest : Path)
    (excluded : a.ap.e.contains f=true) :
    admits (retain a q).ap.tail (retain a q).ap.e (f::rest)=false := by
  have shape := yes
  unfold eligible at shape
  simp only [Bool.and_eq_true] at shape
  have qt : q.ap.tail=.star := by cases t:q.ap.tail <;> simp_all
  have member : f ∈ a.ap.e := List.contains_iff_mem.mp excluded
  simp [retain,yes,admits,qt,member]

theorem the_external_first_field_cap_is_deliberately_relaxed :
    let d : Ap := ⟨0,[],.may,some 7,[],[]⟩
    let a : Offered := ⟨⟨0,[1,2],.must,some 7,[2],[]⟩,false⟩
    let q : Seed := ⟨⟨0,[1,2],.star,some 7,[2],[]⟩,true⟩
    (HeadPolicy.emit 5 8 false d a).contains q=true ∧
      q.ap.path.length>d.path.length+1 ∧ q.ap.path.length≤8 := by decide +kernel

theorem every_relative_cap_exception_has_the_enumerated_certificate
    (run k : Nat) (back : Bool) (d : Ap) (a : Offered) (q : Seed)
    (inside : q ∈ HeadPolicy.emit run k back d a)
    (long : d.path.length+1<q.ap.path.length) :
    ∃ old ∈ CarryPolicy.emit run k back d a,
      capException run back d a old=true ∧ q=retain a old := by
  unfold HeadPolicy.emit at inside
  split at inside
  · have bound := (CarrySafety.emitted_legal run k back d a q inside).2.1
    simp only [NonEmptyPolicy.selector_path] at bound
    omega
  · rename_i active
    rcases List.mem_map.mp inside with ⟨old,oldIn,same⟩
    have yes : eligible a old=true := by
      by_cases h : eligible a old=true
      · exact h
      · have sameOld : retain a old=old := by simp [retain,h]
        rw [sameOld] at same
        have bound := (CarrySafety.emitted_legal run k back d a old oldIn).2.1
        simp only [NonEmptyPolicy.selector_path] at bound
        rw [← same] at long
        omega
    refine ⟨old,oldIn,?_,same.symm⟩
    unfold capException
    rw [yes]
    rw [Bool.eq_false_iff.mpr active]
    rfl

end HeadSafety
