import Std

/- A small constructive branch-and-stream law. This is not a full native AP,
   JVM, trie-layout or analyzer-equivalence model. Native correspondence is the
   explicit final strict-deeper branch in RestrictedInitialPolicy.emit. -/
namespace C2Descendants
inductive Tail where | star | exact | any | must
  deriving DecidableEq, Repr

def canDescend : Tail → Bool
  | .any | .must => true
  | .star | .exact => false

/-- All other native guards and the actual result are abstract parameters.
    A strictly deeper demand first requires ANY or MUST on the actual. -/
def deeperPrimary (tail : Tail) (otherGuards : Bool) (value : Option α) : Option α :=
  if canDescend tail then if otherGuards then value else none else none

def expand (primary : Option α) (companions : α → List α) : List α :=
  match primary with | none => [] | some value => value :: companions value

theorem star_deeper_primary_rejects (guard : Bool) (value : Option α) :
    deeperPrimary .star guard value = none := rfl

theorem exact_deeper_primary_rejects (guard : Bool) (value : Option α) :
    deeperPrimary .exact guard value = none := rfl

theorem no_primary_has_no_companion (companions : α → List α) :
    expand none companions = [] := rfl

theorem blocked_descendant_has_no_family (tail : Tail) (guard : Bool)
    (value : Option α) (companions : α → List α)
    (blocked : canDescend tail = false) :
    expand (deeperPrimary tail guard value) companions = [] := by
  simp [deeperPrimary, blocked, expand]

/-- Removing only empty-output visitors preserves the complete ordered output,
    including duplicates and companion order, before the native set admission. -/
theorem filter_empty_families (items : List β) (keep : β → Bool)
    (family : β → List α)
    (rejected : ∀ item, keep item = false → family item = []) :
    (items.filter keep).flatMap family = items.flatMap family := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    cases flag : keep item with
    | false => simp [flag, rejected item flag, ih]
    | true => simp [flag, ih]

theorem removed_empty_families_create_no_new_result
    (items : List β) (keep : β → Bool) (family : β → List α)
    (rejected : ∀ item, keep item = false → family item = [])
    (result : α) :
    result ∈ (items.filter keep).flatMap family ↔ result ∈ items.flatMap family := by
  rw [filter_empty_families items keep family rejected]

/-- Per query, the pruned work is exactly the strict descendant-node count.
    This does not give query frequency, elapsed time or whole-run complexity. -/
theorem visited_nodes_removed (prefixNodes descendantNodes : Nat) :
    (prefixNodes + 1 + descendantNodes) - (prefixNodes + 1) = descendantNodes := by
  exact Nat.add_sub_cancel_left (prefixNodes + 1) descendantNodes

example : deeperPrimary .any true (some 7) = some 7 := rfl
example : deeperPrimary .must true (some 7) = some 7 := rfl
example : deeperPrimary .star true (some 7) = none := rfl
example : deeperPrimary .exact true (some 7) = none := rfl
/-- The provided element is an executable negative witness. Any later additions
    preserve its membership, so a candidate cannot regain set equality. -/
theorem first_extra_witness_survives (baseline observed rest : List α)
    (witness : α) (seen : witness ∈ observed) (absent : witness ∉ baseline) :
    ∃ value, value ∈ observed ++ rest ∧ value ∉ baseline :=
  ⟨witness, List.mem_append_left rest seen, absent⟩

def sameMembership (left right : List α) : Prop :=
  ∀ value, value ∈ left ↔ value ∈ right

theorem first_extra_witness_rejects_only_this_candidate
    (baseline observed rest : List α) (witness : α)
    (seen : witness ∈ observed) (absent : witness ∉ baseline) :
    ¬sameMembership (observed ++ rest) baseline := by
  intro equality
  exact absent ((equality witness).mp (List.mem_append_left rest seen))

end C2Descendants

#print axioms C2Descendants.star_deeper_primary_rejects
#print axioms C2Descendants.exact_deeper_primary_rejects
#print axioms C2Descendants.no_primary_has_no_companion
#print axioms C2Descendants.blocked_descendant_has_no_family
#print axioms C2Descendants.filter_empty_families
#print axioms C2Descendants.removed_empty_families_create_no_new_result
#print axioms C2Descendants.visited_nodes_removed

#print axioms C2Descendants.first_extra_witness_survives
#print axioms C2Descendants.first_extra_witness_rejects_only_this_candidate
