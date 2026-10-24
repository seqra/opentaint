/-
  Protection and constructive transport extraction for FLOW-backed run-1.
  Rule assignment compares the assigned mark with the triggering conclusion.
  Cycle detection also compares the result with the original premise.
  Histories in this file are proof witnesses, not runtime storage.
-/
import ApSpec.Run1FlowTaintCoverage

namespace ApSpec.FlowBackedProtection
open ApSpec

def cycle (origin incoming outgoing : Mark) : Bool :=
  Nat.beq origin outgoing && !(Nat.beq incoming outgoing)

def ruleFlag (old : Bool) (origin incoming assigned : Mark) : Bool :=
  old || Nat.beq incoming assigned || cycle origin incoming assigned

def callFlag (inputFlag summaryFlag : Bool) (origin incoming outgoing : Mark) : Bool :=
  inputFlag || summaryFlag || cycle origin incoming outgoing

def joinFlag (a b : Bool) : Bool := a || b

theorem assign_same_trigger (old : Bool) (origin t : Mark) :
    ruleFlag old origin t t = true := by simp [ruleFlag]

theorem assign_back_original (old : Bool) (origin incoming : Mark) :
    ruleFlag old origin incoming origin = true := by
  cases h : Nat.beq incoming origin <;> simp [ruleFlag, cycle, h]

theorem local_cycle (old : Bool) (t u : Mark) (_different : Nat.beq u t = false) :
    ruleFlag old t u t = true := assign_back_original old t u

theorem cleaner_assign_back (old : Bool) (origin t : Mark) :
    ruleFlag old origin t t = true := assign_same_trigger old origin t

theorem protected_call (p : Bool) (a b c : Mark) : callFlag p true a b c = true := by
  simp [callFlag]

theorem protected_input (p : Bool) (a b c : Mark) : callFlag true p a b c = true := by
  simp [callFlag]

theorem summary_cycle (p q : Bool) (t u : Mark) (different : Nat.beq u t = false) :
    callFlag p q t u t = true := by simp [callFlag, cycle, different]

theorem ordinary_diagonal (t : Mark) : callFlag false false t t t = false := by
  simp [callFlag, cycle]

theorem diagonal_call_plain {p q : Bool} {t u : Mark}
    (h : callFlag p q t u t = false) : p = false ∧ q = false ∧ u = t := by
  cases p <;> cases q <;> cases he : Nat.beq u t <;>
    simp [callFlag, cycle, he] at h
  exact ⟨rfl, rfl, Nat.eq_of_beq_eq_true he⟩

theorem joined_plain {p q : Bool} (h : joinFlag p q = false) : p = false ∧ q = false := by
  cases p <;> cases q <;> simp [joinFlag] at h ⊢

theorem protected_duplicate (p : Bool) :
    joinFlag p true = true ∧ joinFlag true p = true := by cases p <;> decide

theorem join_commutative (p q : Bool) : joinFlag p q = joinFlag q p := by
  cases p <;> cases q <;> decide

theorem join_idempotent (p : Bool) : joinFlag p p = p := by cases p <;> decide

/-- Op contains the original transport recipe, including its point/context. -/
inductive Derivation (Op : Type) : Mark → Mark → Bool → Type where
  | input (t : Mark) : Derivation Op t t false
  | move {t u p} (d : Derivation Op t u p) (op : Op) : Derivation Op t u p
  | assign {t u p} (d : Derivation Op t u p) (v : Mark) :
      Derivation Op t v (ruleFlag p t u v)
  | cleanerKeep {t u p} (d : Derivation Op t u p) :
      Derivation Op t u (ruleFlag p t u u)
  | call {t u v p q} (caller : Derivation Op t u p) (callee : Derivation Op u v q) :
      Derivation Op t v (callFlag p q t u v)
  | merge {t u p q} (a : Derivation Op t u p) (b : Derivation Op t u q) :
      Derivation Op t u (joinFlag p q)

inductive Transport (Op : Type) where
  | input : Transport Op
  | move (before : Transport Op) (op : Op) : Transport Op
  | call (caller callee : Transport Op) : Transport Op
  | merge (a b : Transport Op) : Transport Op

def barriers {Op t u p} : Derivation Op t u p → Nat
  | .input _ => 0
  | .move d _ => barriers d
  | .assign d _ => barriers d + 1
  | .cleanerKeep d => barriers d + 1
  | .call a b => barriers a + barriers b
  | .merge a b => barriers a + barriers b

def operations {Op t u p} : Derivation Op t u p → List Op
  | .input _ => []
  | .move d op => operations d ++ [op]
  | .assign d _ => operations d
  | .cleanerKeep d => operations d
  | .call a b => operations a ++ operations b
  | .merge a b => operations a ++ operations b

def Transport.operations {Op} : Transport Op → List Op
  | .input => []
  | .move d op => d.operations ++ [op]
  | .call a b => a.operations ++ b.operations
  | .merge a b => a.operations ++ b.operations

def extract? {Op t u p} : Derivation Op t u p → Option (Transport Op)
  | .input _ => some .input
  | .move d op => (extract? d).map (fun x => .move x op)
  | .assign _ _ => none
  | .cleanerKeep _ => none
  | .call a b => do return .call (← extract? a) (← extract? b)
  | .merge a b => do return .merge (← extract? a) (← extract? b)

theorem extract_sound {Op t u p} (d : Derivation Op t u p) (tree : Transport Op)
    (h : extract? d = some tree) :
    barriers d = 0 ∧ tree.operations = operations d := by
  induction d generalizing tree with
  | input => cases h; exact ⟨rfl, rfl⟩
  | move d op ih =>
    cases he : extract? d with
    | none => simp [extract?, he] at h
    | some a =>
      simp [extract?, he] at h
      cases h
      obtain ⟨hb, ho⟩ := ih a he
      exact ⟨hb, by simp [Transport.operations, operations, ho]⟩
  | assign => simp [extract?] at h
  | cleanerKeep => simp [extract?] at h
  | call a b iha ihb =>
    cases ha : extract? a <;> cases hb : extract? b <;> simp [extract?, ha, hb] at h
    case some.some ta tb =>
      cases h
      obtain ⟨hba, hoa⟩ := iha ta ha
      obtain ⟨hbb, hob⟩ := ihb tb hb
      exact ⟨by simp [barriers, hba, hbb], by simp [Transport.operations, operations, hoa, hob]⟩
  | merge a b iha ihb =>
    cases ha : extract? a <;> cases hb : extract? b <;> simp [extract?, ha, hb] at h
    case some.some ta tb =>
      cases h
      obtain ⟨hba, hoa⟩ := iha ta ha
      obtain ⟨hbb, hob⟩ := ihb tb hb
      exact ⟨by simp [barriers, hba, hbb], by simp [Transport.operations, operations, hoa, hob]⟩

theorem plain_diagonal_extracts {Op t u p} (d : Derivation Op t u p)
    (same : u = t) (plain : p = false) : ∃ tree, extract? d = some tree := by
  induction d with
  | input => exact ⟨.input, rfl⟩
  | move d op ih =>
    obtain ⟨tree, ht⟩ := ih same plain
    exact ⟨.move tree op, by simp [extract?, ht]⟩
  | assign d v =>
    subst same
    rw [assign_back_original] at plain
    cases plain
  | cleanerKeep d =>
    rw [cleaner_assign_back] at plain
    cases plain
  | @call t u v p q a b iha ihb =>
    subst same
    obtain ⟨hp, hq, hu⟩ := diagonal_call_plain plain
    obtain ⟨ta, ha⟩ := iha hu hp
    obtain ⟨tb, hb⟩ := ihb hu.symm hq
    exact ⟨.call ta tb, by simp [extract?, ha, hb]⟩
  | merge a b iha ihb =>
    obtain ⟨hp, hq⟩ := joined_plain plain
    obtain ⟨ta, ha⟩ := iha same hp
    obtain ⟨tb, hb⟩ := ihb same hq
    exact ⟨.merge ta tb, by simp [extract?, ha, hb]⟩

structure ReplayWitness {Op t u p} (d : Derivation Op t u p) where
  tree : Transport Op
  computed : extract? d = some tree
  noBarrier : barriers d = 0
  sameOperations : tree.operations = operations d

/-- The executable extractor returns the actual tree; existence supplies no choice. -/
def replayWitness {Op t u p} (d : Derivation Op t u p)
    (same : u = t) (plain : p = false) : ReplayWitness d :=
  match he : extract? d with
  | some tree =>
      let h := extract_sound d tree he
      ⟨tree, he, h.1, h.2⟩
  | none => False.elim (by
      obtain ⟨tree, ht⟩ := plain_diagonal_extracts d same plain
      rw [he] at ht
      cases ht)

#print axioms assign_same_trigger
#print axioms assign_back_original
#print axioms local_cycle
#print axioms cleaner_assign_back
#print axioms protected_call
#print axioms protected_input
#print axioms summary_cycle
#print axioms ordinary_diagonal
#print axioms diagonal_call_plain
#print axioms joined_plain
#print axioms protected_duplicate
#print axioms join_commutative
#print axioms join_idempotent
#print axioms extract_sound
#print axioms plain_diagonal_extracts
#print axioms replayWitness

end ApSpec.FlowBackedProtection
