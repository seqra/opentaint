import SelectedTargetApplication

/-! General-arity terminal join boundary. Products enumerate one contributor
from every bucket. Existing AP matching supplies buckets; validation records the
same call and slot keys. `arityAllowed` is the existing ND grammar decision, not
a new rule. The mathematical empty product is [[]]; no zero-arity ND policy is
selected here. Exact AP geometry and Kotlin KaryJoin are production adapters.
-/
namespace TargetJoin
open SelectedCore SelectedTargetApplication TargetZeroND
set_option autoImplicit false

def products {A : Type} : List (List A) → List (List A)
  | [] => [[]]
  | bucket :: rest => bucket.flatMap fun head => (products rest).map (head :: ·)

inductive Complete {A : Type} : List (List A) → List A → Prop where
  | nil : Complete [] []
  | cons {head : A} {bucket : List A} {rest : List (List A)} {tail : List A}
      (member : head ∈ bucket) (later : Complete rest tail) : Complete (bucket :: rest) (head :: tail)

theorem product_member_iff_complete {A : Type} (buckets : List (List A)) (tuple : List A) :
    tuple ∈ products buckets ↔ Complete buckets tuple := by
  induction buckets generalizing tuple with
  | nil =>
      constructor
      · intro member; have same := List.mem_singleton.mp member; subst tuple; exact .nil
      · intro complete; cases complete; exact List.mem_singleton_self _
  | cons bucket rest ih =>
      constructor
      · intro member
        obtain ⟨head,headMember,mapped⟩ := List.mem_flatMap.mp member
        obtain ⟨tail,tailMember,same⟩ := List.mem_map.mp mapped
        subst tuple
        exact .cons headMember (ih tail |>.mp tailMember)
      · intro complete
        cases complete with
        | cons member later =>
            exact List.mem_flatMap.mpr ⟨_,member,List.mem_map.mpr ⟨_,(ih _).mpr later,rfl⟩⟩

theorem complete_arity {A : Type} {buckets : List (List A)} {tuple : List A}
    (complete : Complete buckets tuple) : tuple.length = buckets.length := by
  induction complete with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih
theorem product_has_required_arity {A : Type} (buckets : List (List A)) (tuple : List A)
    (member : tuple ∈ products buckets) : tuple.length = buckets.length :=
  complete_arity ((product_member_iff_complete _ _).mp member)
theorem complete_has_no_empty_slot {A : Type} {buckets : List (List A)} {tuple : List A}
    (complete : Complete buckets tuple) : ∀ bucket ∈ buckets, bucket ≠ [] := by
  induction complete with
  | nil => intro _ absent; cases absent
  | cons member _ ih =>
      intro query present
      rcases List.mem_cons.mp present with same | later
      · subst query; intro empty; rw [empty] at member; cases member
      · exact ih query later
theorem empty_slot_has_no_product {A : Type} (buckets : List (List A)) (empty : ([] : List A) ∈ buckets) :
    products buckets = [] := by
  cases result : products buckets with
  | nil => rfl
  | cons tuple rest =>
      have member : tuple ∈ products buckets := by rw [result]; exact List.mem_cons.mpr (.inl rfl)
      exact False.elim (complete_has_no_empty_slot ((product_member_iff_complete _ _).mp member) [] empty rfl)

structure Contributor where
  call : Nat
  slot : Nat
  origin : List Nat
  layer : Layer
  deriving DecidableEq, Repr

def validated (call : Nat) : Nat → List (List Contributor) → Bool
  | _, [] => true
  | slot, bucket :: rest =>
      bucket.all (fun c => decide (c.call = call ∧ c.slot = slot)) && validated call (slot + 1) rest
def TupleKeys (call : Nat) : Nat → List Contributor → Prop
  | _, [] => True
  | slot, head :: tail => head.call = call ∧ head.slot = slot ∧ TupleKeys call (slot + 1) tail

theorem validated_complete_tuple_keys (call slot : Nat) (buckets : List (List Contributor))
    (tuple : List Contributor) (valid : validated call slot buckets = true)
    (complete : Complete buckets tuple) : TupleKeys call slot tuple := by
  induction complete generalizing slot with
  | nil => trivial
  | @cons head bucket rest tail member _ ih =>
      have parts : bucket.all (fun c => decide (c.call = call ∧ c.slot = slot)) = true ∧
          validated call (slot + 1) rest = true := by
        simpa only [validated,Bool.and_eq_true] using valid
      have keys := of_decide_eq_true (List.all_eq_true.mp parts.1 _ member)
      exact ⟨keys.1,keys.2,ih (slot + 1) parts.2⟩
theorem tuple_keys_same_call (call slot : Nat) (tuple : List Contributor) (keys : TupleKeys call slot tuple) :
    ∀ contributor ∈ tuple, contributor.call = call := by
  induction tuple generalizing slot with
  | nil => intro _ absent; cases absent
  | cons head tail ih =>
      intro contributor member
      rcases List.mem_cons.mp member with same | later
      · subst contributor; exact keys.1
      · exact ih (slot + 1) keys.2.2 contributor later

def fullOrigin (tuple : List Contributor) : List Nat := dedupExact (tuple.flatMap Contributor.origin)
theorem dedup_empty_iff {A : Type} [DecidableEq A] (values : List A) :
    dedupExact values = [] ↔ values = [] := by
  constructor
  · intro empty
    cases values with
    | nil => rfl
    | cons head rest =>
        have member := (TargetZeroND.dedup_membership head (head :: rest)).mpr (List.mem_cons.mpr (.inl rfl))
        rw [empty] at member
        cases member
  · intro empty; subst values; rfl
theorem full_origin_zero_iff_every_origin_zero (tuple : List Contributor) :
    fullOrigin tuple = [] ↔ ∀ contributor ∈ tuple, contributor.origin = [] := by
  exact (dedup_empty_iff _).trans List.flatMap_eq_nil_iff
theorem full_origin_membership (tuple : List Contributor) (origin : Nat) :
    origin ∈ fullOrigin tuple ↔ ∃ contributor ∈ tuple, origin ∈ contributor.origin := by
  simp only [fullOrigin,TargetZeroND.dedup_membership,List.mem_flatMap]

def normalSupport (native : Layer) (tuple : List Contributor) : Bool :=
  allNormal ⟨true,true,tuple.map Contributor.layer,native⟩
theorem normal_support_iff_every_contributor_normal (native : Layer) (tuple : List Contributor) :
    normalSupport native tuple = true ↔ native = .normal ∧ ∀ c ∈ tuple, c.layer = .normal := by
  constructor
  · intro normal
    have parts := (all_normal_iff _).mp normal
    refine ⟨parts.1,?_⟩
    intro contributor member
    exact parts.2 contributor.layer (List.mem_map.mpr ⟨contributor,member,rfl⟩)
  · rintro ⟨nativeNormal,contributorsNormal⟩
    apply (all_normal_iff _).mpr
    refine ⟨nativeNormal,?_⟩
    intro layer member
    obtain ⟨contributor,present,same⟩ := List.mem_map.mp member
    exact same ▸ contributorsNormal contributor present

structure Row where
  owner : Nat
  original : List Nat
  target : Target
  deriving DecidableEq, Repr
def assemble (direction : Direction) (owner : Nat) (target : Target) (native : Layer)
    (tuple : List Contributor) : Option Row :=
  match direction,target with
  | .backward,.normalTarget _ => none
  | .forward,.normalTarget id =>
      if normalSupport native tuple then some ⟨owner,fullOrigin tuple,.normalTarget id⟩ else none
  | _,.demandTarget => some ⟨owner,fullOrigin tuple,.demandTarget⟩
def join (direction : Direction) (call owner requiredArity : Nat) (arityAllowed : Bool)
    (target : Target) (native : Layer) (buckets : List (List Contributor)) : List Row :=
  if arityAllowed && decide (buckets.length = requiredArity) && validated call 0 buckets then
    (products buckets).filterMap (assemble direction owner target native)
  else []

theorem forward_normal_result_iff_all_normal (owner id : Nat) (native : Layer) (tuple : List Contributor) :
    assemble .forward owner (.normalTarget id) native tuple =
      some ⟨owner,fullOrigin tuple,.normalTarget id⟩ ↔ normalSupport native tuple = true := by
  cases result : normalSupport native tuple <;> simp [assemble,result]
theorem backward_normal_is_ignored (owner id : Nat) (native : Layer) (tuple : List Contributor) :
    assemble .backward owner (.normalTarget id) native tuple = none := rfl
theorem demand_remains_anonymous (direction : Direction) (owner : Nat) (native : Layer) (tuple : List Contributor) :
    assemble direction owner .demandTarget native tuple = some ⟨owner,fullOrigin tuple,.demandTarget⟩ := by
  cases direction <;> rfl

theorem every_complete_permitted_match_is_emitted (direction : Direction) (call owner arity : Nat)
    (target : Target) (native : Layer) (buckets : List (List Contributor)) (tuple : List Contributor)
    (row : Row) (valid : validated call 0 buckets = true) (shape : buckets.length = arity)
    (complete : Complete buckets tuple) (assembled : assemble direction owner target native tuple = some row) :
    row ∈ join direction call owner arity true target native buckets := by
  have admitted : (true && decide (buckets.length = arity) && validated call 0 buckets) = true := by
    simp only [decide_eq_true shape,valid,Bool.true_and]
  unfold join
  rw [if_pos admitted]
  exact List.mem_filterMap.mpr ⟨tuple,(product_member_iff_complete _ _).mpr complete,assembled⟩

theorem denied_arity_emits_nothing (direction : Direction) (call owner arity : Nat)
    (target : Target) (native : Layer) (buckets : List (List Contributor)) :
    join direction call owner arity false target native buckets = [] := rfl

theorem join_has_complete_tuple (direction : Direction) (call owner arity : Nat) (allowed : Bool)
    (target : Target) (native : Layer) (buckets : List (List Contributor)) (row : Row)
    (member : row ∈ join direction call owner arity allowed target native buckets) :
    ∃ tuple, Complete buckets tuple ∧ tuple.length = arity ∧ TupleKeys call 0 tuple ∧
      assemble direction owner target native tuple = some row := by
  unfold join at member
  split at member
  · rename_i ready
    have parts : (allowed = true ∧ decide (buckets.length = arity) = true) ∧ validated call 0 buckets = true := by
      simpa only [Bool.and_eq_true] using ready
    obtain ⟨tuple,tupleMember,assembled⟩ := List.mem_filterMap.mp member
    have complete := (product_member_iff_complete _ _).mp tupleMember
    exact ⟨tuple,complete,(complete_arity complete).trans (of_decide_eq_true parts.1.2),
      validated_complete_tuple_keys call 0 buckets tuple parts.2 complete,assembled⟩
  · cases member

theorem empty_slot_has_no_terminal_join (direction : Direction) (call owner arity : Nat) (allowed : Bool)
    (target : Target) (native : Layer) (buckets : List (List Contributor)) (empty : [] ∈ buckets) :
    join direction call owner arity allowed target native buckets = [] := by
  unfold join
  split
  · rw [empty_slot_has_no_product buckets empty]; rfl
  · rfl
theorem arity_mismatch_has_no_join (direction : Direction) (call owner arity : Nat) (allowed : Bool)
    (target : Target) (native : Layer) (buckets : List (List Contributor)) (wrong : buckets.length ≠ arity) :
    join direction call owner arity allowed target native buckets = [] := by
  have falseArity : decide (buckets.length = arity) = false := decide_eq_false wrong
  simp only [join,falseArity,Bool.and_false,Bool.false_and,Bool.false_eq_true,↓reduceIte]

/-- Search yields the actual complete contributor tuple for a produced row. -/
def findTuple (direction : Direction) (owner : Nat) (target : Target) (native : Layer)
    (buckets : List (List Contributor)) (row : Row) : Option (List Contributor) :=
  (products buckets).find? fun tuple => decide (assemble direction owner target native tuple = some row)
def executableWitness (direction : Direction) (call owner arity : Nat) (allowed : Bool)
    (target : Target) (native : Layer) (buckets : List (List Contributor)) (row : Row)
    (member : row ∈ join direction call owner arity allowed target native buckets) :
    {tuple : List Contributor // Complete buckets tuple ∧ tuple.length = arity ∧
      TupleKeys call 0 tuple ∧ assemble direction owner target native tuple = some row} := by
  have existsTuple := join_has_complete_tuple direction call owner arity allowed target native buckets row member
  have found : (findTuple direction owner target native buckets row).isSome = true := by
    obtain ⟨tuple,complete,_,_,assembled⟩ := existsTuple
    apply List.find?_isSome.mpr
    exact ⟨tuple,(product_member_iff_complete _ _).mpr complete,decide_eq_true assembled⟩
  let tuple := (findTuple direction owner target native buckets row).get found
  have foundTuple : findTuple direction owner target native buckets row = some tuple := Option.eq_some_of_isSome found
  have tupleMember := List.mem_of_find?_eq_some foundTuple
  have assembled : assemble direction owner target native tuple = some row :=
    of_decide_eq_true (List.find?_some (p := fun (candidate : List Contributor) =>
      decide (assemble direction owner target native candidate = some row)) foundTuple)
  refine ⟨tuple,(product_member_iff_complete _ _).mp tupleMember,?_,?_,assembled⟩
  · have arityMatch : buckets.length = arity := by
      unfold join at member
      split at member
      · rename_i ready
        have parts : (allowed = true ∧ decide (buckets.length = arity) = true) ∧
            validated call 0 buckets = true := by
          simpa only [Bool.and_eq_true] using ready
        exact of_decide_eq_true parts.1.2
      · cases member
    exact (product_has_required_arity _ _ tupleMember).trans arityMatch
  · have valid : validated call 0 buckets = true := by
      unfold join at member
      split at member
      · rename_i ready
        have parts : (allowed = true ∧ decide (buckets.length = arity) = true) ∧
            validated call 0 buckets = true := by
          simpa only [Bool.and_eq_true] using ready
        exact parts.2
      · cases member
    exact validated_complete_tuple_keys call 0 buckets tuple valid ((product_member_iff_complete _ _).mp tupleMember)

namespace Controls
def c0 : Contributor := ⟨8,0,[],.normal⟩
def c1 : Contributor := ⟨8,1,[41],.normal⟩
def c2 : Contributor := ⟨8,2,[],.normal⟩
def buckets : List (List Contributor) := [[c0],[c1],[c2]]
def expected : Row := ⟨2,[41],.normalTarget 7⟩
def result := join .forward 8 2 3 true (.normalTarget 7) .normal buckets
def witness := executableWitness .forward 8 2 3 true (.normalTarget 7) .normal buckets expected (by decide)
theorem three_slots_keep_full_nonzero_origin : result = [expected] := by decide
theorem empty_cross_call_wrong_arity_no_completion :
    join .forward 8 2 3 true (.normalTarget 7) .normal [[c0],[],[c2]] = [] ∧
    join .forward 8 2 3 true (.normalTarget 7) .normal [[c0],[{c1 with call := 9}],[c2]] = [] ∧
    join .forward 8 2 4 true (.normalTarget 7) .normal buckets = [] := by decide
theorem normal_only_includes_every_slot_and_native :
    join .forward 8 2 3 true (.normalTarget 7) .normal [[c0],[{c1 with layer := .demand}],[c2]] = [] ∧
    join .forward 8 2 3 true (.normalTarget 7) .demand buckets = [] ∧
    join .forward 8 2 3 true .demandTarget .demand buckets = [⟨2,[41],.demandTarget⟩] := by decide
#eval witness.val
end Controls

end TargetJoin
