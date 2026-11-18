import ReplySupport

namespace DefiniteReplySupport
open NonEmptyPolicy NonEmptyRestriction ExactSupport

local instance : LawfulBEq Tail where
  rfl := by intro a; cases a <;> rfl
  eq_of_beq := by
    intro a b h
    cases a <;> cases b <;> first | rfl | cases h

/-- Legal determinate concrete forms. MUST keeps its real exclusions. -/
def eligible (k : Key) : Bool :=
  k.ap.mark.isSome && k.ap.mx.isEmpty &&
    ((k.ap.tail == .exact && k.ap.e.isEmpty) || k.ap.tail == .must)

def absorb := ReplySupportKernel.absorb eligible
def foldValues (xs : List Value) : List Value :=
  (absorb (xs.map ExactSupportCycle.wrap)).map ExactSupportCycle.unwrap

theorem retained_normal_witness (xs : List Item) (x : Item)
    (present : x ∈ xs) (gone : x ∉ absorb xs) :
    x.demand = true ∧ eligible x.key = true ∧ normal x ∈ absorb xs :=
  ReplySupportKernel.deletion_has_retained_witness eligible xs x present gone

theorem every_normal_reply_is_preserved (xs : List Item) (x : Item)
    (normalSupport : x.demand = false) : x ∈ absorb xs ↔ x ∈ xs :=
  ReplySupportKernel.normal_members_unchanged eligible xs x normalSupport

theorem same_complete_key_and_legal_form (xs : List Item) (x : Item)
    (present : x ∈ xs) (gone : x ∉ absorb xs) :
    (normal x).key = x.key ∧
    (x.key.ap.tail = .exact ∨ x.key.ap.tail = .must) := by
  have h := (retained_normal_witness xs x present gone).2.1
  refine ⟨rfl,?_⟩
  cases ht : x.key.ap.tail <;> simp_all [eligible]

/-- Reuse the proved support-monotone transfer and complete-AND laws. No
    suffix or point in a MUST region is enumerated by the replacement. -/
theorem finite_continuation_preserved (steps : List ((Key → Key) × (Key → Bool)))
    (xs : List Item) (x : Item) (present : x ∈ xs) (gone : x ∉ absorb xs) :
    normal x ∈ absorb xs ∧ stronger (ExactSupport.run steps (normal x))
      (ExactSupport.run steps x) := by
  refine ⟨(retained_normal_witness xs x present gone).2.2,?_⟩
  exact ExactSupport.arbitrary_finite_continuation steps (normal x) x ⟨rfl,Or.inl rfl⟩

theorem complete_nd_binding_preserved (g : List Key → Key) (loss : Bool)
    (x : Item) (rest : List Item) :
    stronger (ExactSupport.joined g loss (normal x :: rest))
      (ExactSupport.joined g loss (x :: rest)) :=
  ExactSupport.complete_nd_binding_is_preserved g loss x rest

def represented (k : Key) (location : Path) : Prop :=
  ∃ rest, location = k.ap.path ++ rest ∧ admits k.ap.tail k.ap.e rest = true

theorem every_location_in_the_uniform_reply_is_preserved (x : Item)
    (location : Path) : represented (normal x).key location ↔ represented x.key location :=
  Iff.rfl

theorem field_exclusions_and_protection_are_literal (x : Item) :
    (normal x).key.ap.e = x.key.ap.e ∧ (normal x).key.h = x.key.h ∧
    (normal x).key.original = x.key.original ∧
    (normal x).key.continuation = x.key.continuation := ⟨rfl,rfl,rfl,rfl⟩

theorem no_work_is_added (xs : List Item) : (absorb xs).length ≤ xs.length :=
  List.length_filter_le _ _

theorem exact_rule_is_included (k : Key) (old : ExactSupport.eligible k = true) :
    eligible k = true := by
  simp only [ExactSupport.eligible,Bool.and_eq_true] at old
  simp [eligible,old.1.1.2,old.2,old.1.2,old.1.1.1]

theorem extension_only_removes_additional_demand (xs : List Item) (x : Item)
    (kept : x ∈ absorb xs) : x ∈ ExactSupport.absorb xs := by
  rcases (ReplySupportKernel.membership eligible xs x).mp kept with ⟨member,reason⟩
  apply (ExactSupport.membership xs x).mpr
  refine ⟨member,?_⟩
  rcases reason with hn | he | absent
  · exact Or.inl hn
  · right; left
    cases h : ExactSupport.eligible x.key
    · rfl
    · have contradiction := exact_rule_is_included x.key h
      rw [he] at contradiction
      cases contradiction
  · exact Or.inr (Or.inr absent)

/-- Support does not select a different geometric head family. In particular,
    a MUST actual starts the same uniform query, with its real E, in both
    layers. The stronger actual changes support, not the query language. -/
theorem head_initial_geometry_is_support_independent (d a : Ap) (n m : Bool) :
    (atHead d ⟨a,n⟩).map Seed.ap = (atHead d ⟨a,m⟩).map Seed.ap := by
  rcases d with ⟨db,dp,dt,dm,de,dx⟩
  rcases a with ⟨ab,ap,actualTail,am,ae,ax⟩
  cases dt <;> cases actualTail <;> rfl

def key (tail : Tail) (e : List Nat := []) (h : Bool := false) : Key :=
  ⟨0,[0],0,⟨1,[],tail,some 2,e,[]⟩,h⟩
def item (tail : Tail) (d : Bool) (e : List Nat := []) (h : Bool := false) : Item :=
  ⟨key tail e h,d⟩

theorem same_literal_uniform_reply_absorbed_in_both_orders :
    absorb [item .must true,item .must false] = [item .must false] ∧
    absorb [item .must false,item .must true] = [item .must false] := by decide

theorem protected_uniform_copies_keep_their_own_class :
    absorb [item .must true [] true,item .must false [] true] = [item .must false [] true] ∧
    absorb [item .must true [] true,item .must false] =
      [item .must true [] true,item .must false] := by decide

theorem matching_real_exclusions_are_preserved :
    absorb [item .must true [7],item .must false [7]] = [item .must false [7]] := by decide

theorem differing_real_exclusions_are_not_compared :
    absorb [item .must true [7],item .must false [8]] =
      [item .must true [7],item .must false [8]] := by decide

theorem a_root_point_does_not_replace_uniform_demand :
    absorb [item .must true,item .exact false] = [item .must true,item .exact false] := by decide

theorem lone_demand_and_may_ne_star_and_flow_are_unchanged :
    absorb [item .must true] = [item .must true] ∧
    ([Tail.may,.ne,.star].all fun tail =>
      decide (absorb [item tail true,item tail false] = [item tail true,item tail false])) = true ∧
    eligible {key .must with ap := {(key .must).ap with mark := none}} = false := by decide

theorem inherited_original_and_continuation_are_not_mixed :
    absorb [⟨{key .must with original := [1]},true⟩,item .must false] =
      [⟨{key .must with original := [1]},true⟩,item .must false] ∧
    absorb [⟨{key .must with continuation := 1},true⟩,item .must false] =
      [⟨{key .must with continuation := 1},true⟩,item .must false] := by decide

end DefiniteReplySupport
