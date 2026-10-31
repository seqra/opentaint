import Std

/-! Literal-coordinate model of the canonical empty-path STAR/FLOW match.
Applicable geometry keeps every coordinate; inside geometry is a subpart.
FULL wildcard marking is identity. This does not model arbitrary AP queries. -/
namespace UniversalRootMatch

abbrev Root (n : Nat) := Fin n → Bool
def union (a b : Root n) : Root n := fun i => a i || b i
def trim (a b : Root n) : Root n := fun i => a i && b i
def included (a b : Root n) : Prop := ∀ i, a i = true → b i = true
inductive Tail where | exact | star | may | must deriving DecidableEq, Repr
inductive Kind where | flow | taint deriving DecidableEq, Repr
inductive Layer where | normal | demand deriving DecidableEq, Repr
structure Header where
  base : Nat
  tail : Tail
  kind : Kind
  layer : Layer
  fieldExclusions : List Nat
  markExclusions : List Nat
  deriving DecidableEq, Repr
structure Actual (n : Nat) where
  header : Header
  ordinary : Root n
  protection : Root n

def rootLeafKept : Tail → Bool
  | .exact | .star | .may | .must => true

def applicableRoot (a : Actual n) (atRoot : Fin n → Bool) : Root n :=
  fun i => a.ordinary i && (if atRoot i then rootLeafKept a.header.tail else true)

def insideRoot (a : Actual n) (selector : Root n) : Root n := trim a.ordinary selector

def legacyGeometry (a : Actual n) (atRoot selector : Root n) : Root n :=
  union (applicableRoot a atRoot) (insideRoot a selector)

def fullWildcardFilter (r : Root n) : Root n := fun i => r i && !false

def legacyUniversal (a : Actual n) (atRoot selector : Root n) : Actual n :=
  let root := fullWildcardFilter (legacyGeometry a atRoot selector)
  ⟨a.header, root, trim a.protection root⟩

def newUniversal (a : Actual n) : Actual n := a

def belowEnabled (record run1 : Bool) : Bool := record || run1 || (!run1 && true)

theorem below_enabled_in_every_mode (record run1 : Bool) : belowEnabled record run1 = true := by
  cases record <;> cases run1 <;> rfl

theorem all_legal_tails_keep_root (t : Tail) : rootLeafKept t = true := by cases t <;> rfl

theorem applicable_root_is_complete (a : Actual n) (atRoot : Root n) : applicableRoot a atRoot = a.ordinary := by
  funext i
  simp [applicableRoot, all_legal_tails_keep_root]

theorem inside_root_is_subset (a : Actual n) (selector : Root n) :
    included (insideRoot a selector) a.ordinary := by
  intro i h
  exact (Bool.and_eq_true_iff.mp h).1

theorem universal_geometry_is_complete (a : Actual n) (atRoot selector : Root n) :
    legacyGeometry a atRoot selector = a.ordinary := by
  rw [legacyGeometry, applicable_root_is_complete]
  funext i
  cases h : a.ordinary i <;> simp [union, insideRoot, trim, h]

theorem full_wildcard_mark_filter_is_identity (r : Root n) : fullWildcardFilter r = r := by
  funext i; simp [fullWildcardFilter]

theorem mask_trim_is_identity (a : Actual n) (h : included a.protection a.ordinary) :
    trim a.protection a.ordinary = a.protection := by
  funext i
  cases hp : a.protection i with
  | false => simp [trim, hp]
  | true => simp [trim, hp, h i hp]

theorem complete_actual_and_header_preserved (a : Actual n) (atRoot selector : Root n)
    (h : included a.protection a.ordinary) : legacyUniversal a atRoot selector = newUniversal a := by
  simp [legacyUniversal, newUniversal, universal_geometry_is_complete,
    full_wildcard_mark_filter_is_identity, mask_trim_is_identity a h]

theorem protection_preserved (a : Actual n) (atRoot selector : Root n)
    (h : included a.protection a.ordinary) :
    (legacyUniversal a atRoot selector).protection = a.protection := by
  rw [complete_actual_and_header_preserved a atRoot selector h]; rfl

theorem field_mark_exclusions_and_layer_preserved (a : Actual n) (atRoot selector : Root n) :
    (legacyUniversal a atRoot selector).header = a.header := rfl

/-- Only wildcard mark-map coordinate visits are counted, not total Kotlin time. -/
def oldMarkMapVisits (n : Nat) : Nat := (List.finRange n).length
def newMarkMapVisits (_n : Nat) : Nat := 0

theorem all_mark_map_visits_removed (n : Nat) :
    oldMarkMapVisits n = n ∧ newMarkMapVisits n = 0 := by
  simp [oldMarkMapVisits, newMarkMapVisits]

theorem positive_images_have_fewer_mark_map_visits (n : Nat) (h : 0 < n) :
    newMarkMapVisits n < oldMarkMapVisits n := by
  simpa [oldMarkMapVisits, newMarkMapVisits] using h

end UniversalRootMatch
