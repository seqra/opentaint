import MustCycle

/- Exact FULL data has no residual suffix to refine. Preserve the complete
   caller original, continuation and literal protection before comparing it.
   This module changes neither native matching nor the native record basis. -/
namespace ExactSupport
open NonEmptyPolicy NonEmptyRestriction

structure Key where
  frame : Nat
  original : List Nat
  continuation : Nat
  ap : Ap
  h : Bool
  deriving DecidableEq, Repr

structure Item where
  key : Key
  demand : Bool
  deriving DecidableEq, Repr

def eligible (k : Key) : Bool :=
  k.ap.tail == .exact && k.ap.mark.isSome && k.ap.e.isEmpty && k.ap.mx.isEmpty

def normal (x : Item) : Item := {x with demand := false}

def absorb (packet : List Item) : List Item :=
  packet.filter fun x => !x.demand || !eligible x.key || !decide (normal x ∈ packet)

theorem normal_is_normal (x : Item) : (normal x).demand = false := rfl
theorem normal_keeps_complete_key (x : Item) : (normal x).key = x.key := rfl

theorem membership (xs : List Item) (x : Item) :
    x ∈ absorb xs ↔ x ∈ xs ∧
      (x.demand = false ∨ eligible x.key = false ∨ normal x ∉ xs) := by
  simp [absorb,Bool.or_eq_true,or_assoc]

theorem subset (xs : List Item) (x : Item) (hx : x ∈ absorb xs) : x ∈ xs :=
  ((membership xs x).mp hx).1

theorem all_normal_members_retained (xs : List Item) (x : Item)
    (hx : x ∈ xs) (hn : x.demand = false) : x ∈ absorb xs := by
  exact (membership xs x).mpr ⟨hx,Or.inl hn⟩

theorem normal_members_unchanged (xs : List Item) (x : Item) (hn : x.demand = false) :
    x ∈ absorb xs ↔ x ∈ xs :=
  ⟨subset xs x, fun hx => all_normal_members_retained xs x hx hn⟩

theorem missing_normal_keeps_demand (xs : List Item) (x : Item)
    (hx : x ∈ xs) (missing : normal x ∉ xs) : x ∈ absorb xs :=
  (membership xs x).mpr ⟨hx,Or.inr (Or.inr missing)⟩

theorem unsupported_members_retained (xs : List Item) (x : Item)
    (hx : x ∈ xs) (unsupported : eligible x.key = false) : x ∈ absorb xs :=
  (membership xs x).mpr ⟨hx,Or.inr (Or.inl unsupported)⟩

/-- The deleted member has an explicit retained NORMAL witness, with every
    scope, premise, mark, field, protection and resume coordinate unchanged. -/
theorem deletion_has_retained_witness (xs : List Item) (x : Item)
    (hx : x ∈ xs) (gone : x ∉ absorb xs) :
    x.demand = true ∧ eligible x.key = true ∧ normal x ∈ absorb xs := by
  have hd : x.demand = true := by
    cases h : x.demand
    · exact False.elim (gone (all_normal_members_retained xs x hx h))
    · rfl
  have he : eligible x.key = true := by
    cases h : eligible x.key
    · exact False.elim (gone (unsupported_members_retained xs x hx h))
    · rfl
  have hm : normal x ∈ xs := by
    by_cases h : normal x ∈ xs
    · exact h
    · exact False.elim (gone (missing_normal_keeps_demand xs x hx h))
  exact ⟨hd,he,all_normal_members_retained xs (normal x) hm rfl⟩

theorem same_observable_keys (xs : List Item) (k : Key) :
    (∃ x ∈ xs, x.key = k) ↔ ∃ x ∈ absorb xs, x.key = k := by
  constructor
  · rintro ⟨x,hx,hk⟩
    by_cases h : x ∈ absorb xs
    · exact ⟨x,h,hk⟩
    · exact ⟨normal x,(deletion_has_retained_witness xs x hx h).2.2,hk⟩
  · rintro ⟨x,hx,hk⟩; exact ⟨x,subset xs x hx,hk⟩

theorem idempotent_membership (xs : List Item) (x : Item) :
    x ∈ absorb (absorb xs) ↔ x ∈ absorb xs := by
  constructor
  · exact subset (absorb xs) x
  · intro hx
    apply (membership (absorb xs) x).mpr
    refine ⟨hx,?_⟩
    rcases ((membership xs x).mp hx).2 with hn | he | hm
    · exact Or.inl hn
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (fun h => hm (subset xs (normal x) h)))

theorem order_independent (xs ys : List Item)
    (same : ∀ x, x ∈ xs ↔ x ∈ ys) (x : Item) :
    x ∈ absorb xs ↔ x ∈ absorb ys := by
  simp only [membership,same]

theorem merge_membership (xs ys : List Item) (x : Item) :
    x ∈ absorb (absorb xs ++ ys) ↔ x ∈ absorb (xs ++ ys) := by
  have hn := normal_members_unchanged xs (normal x) rfl
  rw [membership,membership]
  simp only [List.mem_append]
  constructor
  · rintro ⟨hx,hfilter⟩
    refine ⟨hx.elim (fun h => Or.inl (subset xs x h)) Or.inr,?_⟩
    simpa only [hn] using hfilter
  · rintro ⟨hx,hfilter⟩
    refine ⟨?_,?_⟩
    · rcases hx with hx | hx
      · left
        apply (membership xs x).mpr
        refine ⟨hx,?_⟩
        rcases hfilter with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (fun hm => h (Or.inl hm)))
      · exact Or.inr hx
    · simpa only [hn] using hfilter

/-- A path of ordinary support-monotone transfers. The operator owns all
    geometry/mark/protection changes; the layer is its native join with loss. -/
def transfer (geometry : Key → Key) (loss : Key → Bool) (x : Item) : Item :=
  ⟨geometry x.key,x.demand || loss x.key⟩

def stronger (a b : Item) : Prop :=
  a.key = b.key ∧ (a.demand = false ∨ a.demand = b.demand)

theorem retained_witness_is_stronger (xs : List Item) (x : Item)
    (hx : x ∈ xs) (gone : x ∉ absorb xs) :
    normal x ∈ absorb xs ∧ stronger (normal x) x :=
  ⟨(deletion_has_retained_witness xs x hx gone).2.2,⟨rfl,Or.inl rfl⟩⟩

theorem transfer_monotone (g : Key → Key) (loss : Key → Bool)
    (a b : Item) (h : stronger a b) :
    stronger (transfer g loss a) (transfer g loss b) := by
  rcases a with ⟨ak,ad⟩; rcases b with ⟨bk,bd⟩
  rcases h with ⟨hk,hl⟩; cases hk
  change g ak = g ak ∧ ((ad || loss ak) = false ∨ (ad || loss ak) = (bd || loss ak))
  refine ⟨rfl,?_⟩
  cases ad <;> cases bd <;> cases loss ak <;> simp_all

def run (steps : List ((Key → Key) × (Key → Bool))) (x : Item) : Item :=
  steps.foldl (fun a s => transfer s.1 s.2 a) x

theorem arbitrary_finite_continuation (steps : List ((Key → Key) × (Key → Bool)))
    (a b : Item) (h : stronger a b) : stronger (run steps a) (run steps b) := by
  induction steps generalizing a b with
  | nil => exact h
  | cons first rest ih =>
      exact ih _ _ (transfer_monotone first.1 first.2 a b h)

theorem normal_final_result_not_lost (steps : List ((Key → Key) × (Key → Bool)))
    (xs : List Item) (x : Item) (hx : x ∈ xs) (gone : x ∉ absorb xs)
    (hn : (run steps x).demand = false) :
    (run steps (normal x)).key = (run steps x).key ∧
      (run steps (normal x)).demand = false := by
  have h := arbitrary_finite_continuation steps (normal x) x
    (retained_witness_is_stronger xs x hx gone).2
  exact ⟨h.1,h.2.elim id (fun same => same.trans hn)⟩

/-- Call only after a complete AND binding has been found. All input keys
    still participate; replacing one support does not remove a premise. -/
def joined (geometry : List Key → Key) (loss : Bool) (inputs : List Item) : Item :=
  ⟨geometry (inputs.map Item.key),inputs.any Item.demand || loss⟩

theorem complete_nd_binding_is_preserved (g : List Key → Key) (loss : Bool)
    (x : Item) (rest : List Item) :
    stronger (joined g loss (normal x :: rest)) (joined g loss (x :: rest)) := by
  unfold joined stronger normal
  simp only [List.map_cons,List.any_cons]
  refine ⟨by trivial,?_⟩
  cases x.demand <;> cases rest.any Item.demand <;> cases loss <;> decide

theorem normal_join_does_not_borrow_demand_input (g : List Key → Key)
    (loss : Bool) (x : Item) (rest : List Item) (hd : x.demand = true) :
    (joined g loss (x :: rest)).demand = true := by
  simp [joined,hd]

theorem no_path_or_work_added (xs : List Item) : (absorb xs).length ≤ xs.length :=
  List.length_filter_le _ _

def key (path : Path := []) (h : Bool := false) : Key :=
  ⟨0,[0],0,⟨1,path,.exact,some 2,[],[]⟩,h⟩
def point (d : Bool) : Item := ⟨key [],d⟩

theorem both_orders_keep_only_normal :
    absorb [point true,point false] = [point false] ∧
    absorb [point false,point true] = [point false] := by decide

theorem literal_protection_is_not_mixed :
    absorb [⟨key [] true,true⟩,point false] = [⟨key [] true,true⟩,point false] := by decide

theorem distinct_complete_originals_are_not_mixed :
    absorb [⟨{key [] with original := [1]},true⟩,point false] =
      [⟨{key [] with original := [1]},true⟩,point false] := by decide

theorem different_continuations_are_not_mixed :
    absorb [⟨{key [] with continuation := 1},true⟩,point false] =
      [⟨{key [] with continuation := 1},true⟩,point false] := by decide

theorem different_marks_and_paths_are_not_mixed :
    absorb [⟨{key [] with ap := { (key []).ap with mark := some 3}},true⟩,
      ⟨key [1],true⟩,point false] =
      [⟨{key [] with ap := { (key []).ap with mark := some 3}},true⟩,
       ⟨key [1],true⟩,point false] := by decide

theorem uncertain_tails_are_not_absorbed_by_location_inclusion :
    let mayKey := {key [] with ap := { (key []).ap with tail := .may}}
    absorb [⟨mayKey,true⟩,⟨mayKey,false⟩] = [⟨mayKey,true⟩,⟨mayKey,false⟩] := by decide

end ExactSupport
