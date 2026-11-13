import Std
namespace BlockAliasClosureBoundary

-- Two names for one marked cell. This is a small interface projection model,
-- not a model of JIR alias analysis or complete native block services.
inductive Name where | x | y deriving DecidableEq
structure Coverage where
  x : Bool
  y : Bool

def parent : Coverage := ⟨true, true⟩
def selectX (s : Coverage) : Coverage := ⟨s.x, false⟩
def aliasCovered (s : Coverage) : Prop := s.x = true ∧ s.y = true

theorem parent_covers_both_names : aliasCovered parent := ⟨rfl, rfl⟩
theorem selected_X_is_kept : (selectX parent).x = true := by rfl
theorem owned_projection_is_not_full_alias_closure : ¬ aliasCovered (selectX parent) := by
  intro h
  have bad : false = true := h.2
  cases bad

-- Backward liveness has no kill. Any finite path to a real mention makes
-- the start live. A genuine-alias -> definition-path adapter is NOT assumed.
inductive MentionPath (edge : N → N → Prop) (mention : N → Bool) : N → Prop where
 | here (n : N) : mention n = true → MentionPath edge mention n
 | next (n m : N) : edge n m → MentionPath edge mention m → MentionPath edge mention n

structure ClosedLive (edge : N → N → Prop) (mention live : N → Bool) : Prop where
 here : ∀ n, mention n = true → live n = true
 next : ∀ n m, edge n m → live m = true → live n = true

theorem mention_path_is_live (edge : N → N → Prop) (mention live : N → Bool)
 (h : ClosedLive edge mention live) (n : N) (path : MentionPath edge mention n) : live n = true := by
 induction path with
 | here n yes => exact h.here n yes
 | next n m e p ih => exact h.next n m e ih

theorem dead_has_no_mention_path (edge : N → N → Prop) (mention live : N → Bool)
 (h : ClosedLive edge mention live) (n : N) (dead : live n = false) :
 MentionPath edge mention n → False := by
 intro path
 have yes := mention_path_is_live edge mention live h n path
 rw [dead] at yes
 cases yes

-- Initialization witness for a finite reverse execution prefix. Local names
-- start absent. Actual JIR extraction and genuine-alias validity are adapters.
structure Inst where
 definesX : Bool
 mentionsX : Bool

def initialized : List Inst → Bool
 | [] => false
 | i :: rest => i.definesX || initialized rest

inductive DefinitionAt : List Inst → Type where
 | here {i : Inst} {rest : List Inst} : i.definesX = true → DefinitionAt (i :: rest)
 | there {i : Inst} {rest : List Inst} : DefinitionAt rest → DefinitionAt (i :: rest)

inductive MentionAt : List Inst → Type where
 | here {i : Inst} {rest : List Inst} : i.mentionsX = true → MentionAt (i :: rest)
 | there {i : Inst} {rest : List Inst} : MentionAt rest → MentionAt (i :: rest)

def definitionWitness : (trace : List Inst) → initialized trace = true → DefinitionAt trace
 | [], h => nomatch h
 | i :: rest, h =>
   match hd : i.definesX with
   | true => DefinitionAt.here hd
   | false => DefinitionAt.there (definitionWitness rest (by
       change (i.definesX || initialized rest) = true at h
       rw [hd] at h
       exact h))

def AllDefinitionsMentioned : List Inst → Prop
 | [] => True
 | i :: rest => (i.definesX = true → i.mentionsX = true) ∧ AllDefinitionsMentioned rest

def definitionToMention : (trace : List Inst) → AllDefinitionsMentioned trace → DefinitionAt trace → MentionAt trace
 | [], _, d => nomatch d
 | _i :: _rest, h, DefinitionAt.here d => MentionAt.here (h.1 d)
 | _i :: rest, h, DefinitionAt.there d => MentionAt.there (definitionToMention rest h.2 d)

def initializedMentionWitness (trace : List Inst) (h : AllDefinitionsMentioned trace)
 (yes : initialized trace = true) : MentionAt trace :=
 definitionToMention trace h (definitionWitness trace yes)

#print axioms parent_covers_both_names
#print axioms selected_X_is_kept
#print axioms owned_projection_is_not_full_alias_closure
#print axioms mention_path_is_live
#print axioms dead_has_no_mention_path
#print axioms definitionWitness
#print axioms definitionToMention
#print axioms initializedMentionWitness
end BlockAliasClosureBoundary
