/-
PROPOSAL ONLY, 2026-10-28. This file does not select or implement a runtime change.

Scope: value-level transfer of an unobservable save/clear/restore block. The
payload can include a concrete mark, path suffix and exclusions. This model
does not claim identical abstract AP edges, protection flags, diagnostics or
intermediate layers. JVM lowering, rule observation and alias adapters remain
separate proof obligations in the design proposal.
-/
import Init

namespace DemandStorageNext.SpringCleanup
set_option autoImplicit false
set_option smartUnfolding false

inductive Owner where
  | registry | external
  deriving DecidableEq

inductive Atom (Payload : Type) where
  | zero
  | callerLocal (slot : Nat) (payload : Payload)
  | staticField (owner : Owner) (field : Nat) (payload : Payload)
  deriving DecidableEq

abbrev Saved (Payload : Type) := Option (Nat × Payload)

def saveRegistry {P : Type} : Atom P → Saved P
  | .zero => none
  | .callerLocal _ _ => none
  | .staticField owner f p => match owner with
    | .registry => some (f, p)
    | .external => none

def clearStatics {P : Type} : Atom P → Option (Atom P)
  | .zero => some .zero
  | .callerLocal s p => some (.callerLocal s p)
  | .staticField _ _ _ => none

def restoreRegistry {P : Type} (saved : Saved P) (remaining : Option (Atom P)) :
    Option (Atom P) :=
  match saved with
  | none => remaining
  | some (f, p) => some (.staticField .registry f p)

def oldBlock {P : Type} (input : Atom P) : Option (Atom P) :=
  restoreRegistry (saveRegistry input) (clearStatics input)

/-- A complete contract: missing static rows are kills, not fallback identities. -/
def definedCleanup {P : Type} : Atom P → Option (Atom P)
  | .zero => some .zero
  | .callerLocal s p => some (.callerLocal s p)
  | .staticField owner f p => match owner with
    | .registry => some (.staticField .registry f p)
    | .external => none

theorem value_transfer_equal {P : Type} (input : Atom P) :
    oldBlock input = definedCleanup input := by
  cases input with
  | zero => rfl
  | callerLocal _ _ => rfl
  | staticField owner _ _ => cases owner <;> rfl

def backwardOld {P : Type} (need before : Atom P) : Prop := oldBlock before = some need
def backwardDefined {P : Type} (need before : Atom P) : Prop := definedCleanup before = some need

theorem backward_relation_equal {P : Type} (need before : Atom P) :
    backwardOld need before ↔ backwardDefined need before := by
  change oldBlock before = some need ↔ definedCleanup before = some need
  rw [value_transfer_equal]

theorem registry_payload_unchanged {P : Type} (field : Nat) (payload : P) :
    definedCleanup (.staticField .registry field payload) =
      some (.staticField .registry field payload) := rfl

theorem external_static_killed {P : Type} (field : Nat) (payload : P) :
    definedCleanup (.staticField .external field payload) = none := rfl

theorem zero_does_not_create_registry {P : Type} (field : Nat) (payload : P) :
    definedCleanup (Atom.zero : Atom P) ≠ some (.staticField .registry field payload) := by
  intro h
  change some (Atom.zero : Atom P) = some (.staticField .registry field payload) at h
  cases h

theorem zero_control_preserved {P : Type} :
    definedCleanup (Atom.zero : Atom P) = some .zero := rfl

/-- Ordinary caller locals bypass a zero-argument, void cleanup call. -/
theorem caller_local_preserved {P : Type} (slot : Nat) (payload : P) :
    definedCleanup (.callerLocal slot payload) = some (.callerLocal slot payload) := rfl

inductive Layer where
  | normal | demand
  deriving DecidableEq

/-- The model is exact NORMAL. Existing incoming DEMAND is never strengthened.
    Run-1's existing all-static-DEMAND policy still applies. -/
def staticResultLayer (run1 : Bool) (incoming : Layer) : Layer :=
  if run1 then .demand else incoming

theorem incoming_demand_preserved (run1 : Bool) :
    staticResultLayer run1 .demand = .demand := by
  cases run1 <;> rfl

theorem later_normal_stays_normal : staticResultLayer false .normal = .normal := rfl
theorem run1_static_stays_demand (incoming : Layer) :
    staticResultLayer true incoming = .demand := rfl

/-- A fact-level identity is not a per-registry-field IR expansion. -/
def oldScaffoldInstructions (registryFields : Nat) : Nat := 2 * registryFields + 1
def newScaffoldInstructions : Nat := 1

theorem generated_instruction_saving (registryFields : Nat) :
    oldScaffoldInstructions registryFields = 2 * registryFields + newScaffoldInstructions := rfl

#print axioms value_transfer_equal
#print axioms backward_relation_equal
#print axioms registry_payload_unchanged
#print axioms external_static_killed
#print axioms zero_does_not_create_registry
#print axioms zero_control_preserved
#print axioms caller_local_preserved
#print axioms incoming_demand_preserved
#print axioms later_normal_stays_normal
#print axioms run1_static_stays_demand
#print axioms generated_instruction_saving

end DemandStorageNext.SpringCleanup
