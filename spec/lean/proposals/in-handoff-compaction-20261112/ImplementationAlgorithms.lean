import Std

/- Private implementation algorithms. Provider IDs stand for complete,
   already checked native service witnesses. Cells keep literal coordinates.
   These lemmas add no MAY progress or native matching assumption. -/
namespace ImplementationAlgorithms
set_option autoImplicit false

def without (removed : Nat) (kept : List Nat) : List Nat :=
  kept.filter (fun id => id != removed)

def Valid (kept providers : List Nat) : Prop :=
  ∀ id, id ∈ providers → id ∈ kept

theorem mem_without (removed id : Nat) (kept : List Nat) :
    id ∈ without removed kept ↔ id ∈ kept ∧ id ≠ removed := by
  simp [without]

theorem unaffected_certificate (removed : Nat) (kept providers : List Nat)
    (valid : Valid kept providers) (unaffected : removed ∉ providers) :
    Valid (without removed kept) providers := by
  intro id mem
  apply (mem_without removed id kept).mpr
  refine ⟨valid id mem, ?_⟩
  intro same
  subst id
  exact unaffected mem

def rebind (removed : Nat) (repair : List Nat → List Nat)
    (certificates : List (List Nat)) : List (List Nat) :=
  certificates.map (fun ps => if removed ∈ ps then repair ps else ps)

theorem rebind_valid (removed : Nat) (kept : List Nat)
    (certificates : List (List Nat)) (repair : List Nat → List Nat)
    (oldValid : ∀ ps, ps ∈ certificates → Valid kept ps)
    (repaired : ∀ ps, ps ∈ certificates → removed ∈ ps →
      Valid (without removed kept) (repair ps)) :
    ∀ ps, ps ∈ rebind removed repair certificates →
      Valid (without removed kept) ps := by
  intro ps mem
  obtain ⟨old, oldMem, eq⟩ := List.mem_map.mp mem
  by_cases affected : removed ∈ old
  · have same : repair old = ps := by simpa [affected] using eq
    exact same ▸ repaired old oldMem affected
  · have same : old = ps := by simpa [affected] using eq
    exact same ▸ unaffected_certificate removed kept old (oldValid old oldMem) affected

theorem new_certificate_and_repair (removed : Nat) (kept newProviders : List Nat)
    (certificates : List (List Nat)) (repair : List Nat → List Nat)
    (oldValid : ∀ ps, ps ∈ certificates → Valid kept ps)
    (repaired : ∀ ps, ps ∈ certificates → removed ∈ ps →
      Valid (without removed kept) (repair ps))
    (newValid : Valid (without removed kept) newProviders) :
    ∀ ps, ps ∈ newProviders :: rebind removed repair certificates →
      Valid (without removed kept) ps := by
  intro ps mem
  cases List.mem_cons.mp mem with
  | inl eq => exact eq ▸ newValid
  | inr rest => exact rebind_valid removed kept certificates repair oldValid repaired ps rest

structure Cell where
  geometry : Nat
  source : Nat
  target : Nat
  deriving DecidableEq, Repr

def sourceView (source : Nat) : List Cell → List Cell
  | [] => []
  | c :: rest => if c.source = source then c :: sourceView source rest else sourceView source rest

def eraseSource (source : Nat) : List Cell → List Cell
  | [] => []
  | c :: rest => if c.source = source then eraseSource source rest else c :: eraseSource source rest

theorem other_sources_preserved (source other : Nat) (cells : List Cell)
    (different : other ≠ source) :
    sourceView other (eraseSource source cells) = sourceView other cells := by
  induction cells with
  | nil => rfl
  | cons c rest ih =>
    by_cases hs : c.source = source
    · have ho : c.source ≠ other := by
        intro same
        exact different (same.symm.trans hs)
      simpa only [eraseSource, ite_eq_left hs, sourceView, ite_eq_right ho] using ih
    · by_cases ho : c.source = other
      · simpa only [eraseSource, ite_eq_right hs, sourceView, ite_eq_left ho] using
          congrArg (List.cons c) ih
      · simpa only [eraseSource, ite_eq_right hs, sourceView, ite_eq_right ho] using ih

theorem migrated_source_removed (source : Nat) (cells : List Cell) :
    sourceView source (eraseSource source cells) = [] := by
  induction cells with
  | nil => rfl
  | cons c rest ih =>
    by_cases hs : c.source = source <;>
      simp [sourceView, eraseSource, hs, ih]

theorem partition_membership (source : Nat) (cells : List Cell) (c : Cell) :
    c ∈ cells ↔ c ∈ sourceView source cells ∨ c ∈ eraseSource source cells := by
  induction cells with
  | nil => simp [sourceView, eraseSource]
  | cons x rest ih =>
    by_cases hs : x.source = source
    · simp only [sourceView, eraseSource, hs, ↓reduceIte, List.mem_cons]
      rw [ih, or_assoc]
    · simp only [sourceView, eraseSource, hs, ↓reduceIte, List.mem_cons]
      rw [ih]
      exact or_left_comm

structure Migration where
  packed : List Cell
  scalar : List Cell
  handle : Nat

def migrate (cells : List Cell) (source handle : Nat)
    (nativeJoin : List Cell → List Cell) : Migration :=
  ⟨eraseSource source cells, nativeJoin (sourceView source cells), handle⟩

theorem migration_complete (cells : List Cell) (source handle : Nat)
    (nativeJoin : List Cell → List Cell) :
    (migrate cells source handle nativeJoin).scalar = nativeJoin (sourceView source cells) := rfl

theorem migration_keeps_handle (cells : List Cell) (source handle : Nat)
    (nativeJoin : List Cell → List Cell) :
    (migrate cells source handle nativeJoin).handle = handle := rfl

theorem migration_preserves_others (cells : List Cell) (source other handle : Nat)
    (nativeJoin : List Cell → List Cell) (different : other ≠ source) :
    sourceView other (migrate cells source handle nativeJoin).packed = sourceView other cells :=
  other_sources_preserved source other cells different

theorem migration_one_authority (cells : List Cell) (source handle : Nat)
    (nativeJoin : List Cell → List Cell) :
    sourceView source (migrate cells source handle nativeJoin).packed = [] :=
  migrated_source_removed source cells

theorem final_provider_fixture :
    Valid [1] [1,1] ∧ ¬ Valid [1] [2] := by
  constructor
  · intro id mem
    simpa using mem
  · intro valid
    have impossible := valid 2 (by simp)
    simp at impossible

theorem migration_fixture :
    let cells := [Cell.mk 7 1 2, Cell.mk 7 3 4, Cell.mk 9 1 4]
    sourceView 1 cells = [Cell.mk 7 1 2, Cell.mk 9 1 4] ∧
    sourceView 3 (eraseSource 1 cells) = [Cell.mk 7 3 4] := by decide

#print axioms mem_without
#print axioms unaffected_certificate
#print axioms rebind_valid
#print axioms new_certificate_and_repair
#print axioms other_sources_preserved
#print axioms migrated_source_removed
#print axioms partition_membership
#print axioms migration_complete
#print axioms migration_keeps_handle
#print axioms migration_preserves_others
#print axioms migration_one_authority
#print axioms final_provider_fixture
#print axioms migration_fixture
end ImplementationAlgorithms
