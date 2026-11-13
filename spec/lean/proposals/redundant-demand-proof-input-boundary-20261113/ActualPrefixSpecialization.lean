import Std
namespace ActualPrefixSpecialization

structure Relation where
  input : List Nat
  output : List Nat

private theorem appendAssoc (a b c : List Nat) : (a ++ b) ++ c = a ++ (b ++ c) := by
  induction a with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

-- Only word correlation. Native empty-E, FLOW, scope, role and NORMAL
-- side conditions are checked in the literal JSON audit, not proved here.
theorem same_shift_all_suffixes (n c : Relation) (shift : List Nat)
    (hi : c.input = n.input ++ shift) (ho : c.output = n.output ++ shift)
    (suffix : List Nat) :
    n.input ++ (shift ++ suffix) = c.input ++ suffix ∧
    n.output ++ (shift ++ suffix) = c.output ++ suffix := by
  constructor
  · rw [hi, appendAssoc]
  · rw [ho, appendAssoc]

inductive Shape where
  | rr | rb | rs | er | br | bb | bs | ber | sr | sb | ss | ser

def candidate : Shape → Relation
  | .rr => ⟨[],[]⟩ | .rb => ⟨[],[0]⟩ | .rs => ⟨[],[1]⟩
  | .er => ⟨[2],[]⟩ | .br => ⟨[0],[]⟩ | .bb => ⟨[0],[0]⟩
  | .bs => ⟨[0],[1]⟩ | .ber => ⟨[0,2],[]⟩ | .sr => ⟨[1],[]⟩
  | .sb => ⟨[1],[0]⟩ | .ss => ⟨[1],[1]⟩ | .ser => ⟨[1,2],[]⟩

def provider (s : Shape) : Relation :=
  match s with
  | .bb => ⟨[],[]⟩
  | .ss => ⟨[],[]⟩
  | .rr => ⟨[],[]⟩ | .rb => ⟨[],[0]⟩ | .rs => ⟨[],[1]⟩
  | .er => ⟨[2],[]⟩ | .br => ⟨[0],[]⟩ | .bs => ⟨[0],[1]⟩
  | .ber => ⟨[0,2],[]⟩ | .sr => ⟨[1],[]⟩
  | .sb => ⟨[1],[0]⟩ | .ser => ⟨[1,2],[]⟩

def shift : Shape → List Nat
  | .bb => [0] | .ss => [1]
  | .rr => [] | .rb => [] | .rs => [] | .er => [] | .br => []
  | .bs => [] | .ber => [] | .sr => [] | .sb => [] | .ser => []

theorem twelve_prefix_witnesses (s : Shape) :
    (candidate s).input = (provider s).input ++ shift s ∧
    (candidate s).output = (provider s).output ++ shift s := by
  cases s <;> exact ⟨rfl,rfl⟩

theorem twelve_witnesses_preserve_arbitrary_suffix (s : Shape) (suffix : List Nat) :
    (provider s).input ++ (shift s ++ suffix) = (candidate s).input ++ suffix ∧
    (provider s).output ++ (shift s ++ suffix) = (candidate s).output ++ suffix :=
  same_shift_all_suffixes (provider s) (candidate s) (shift s)
    (twelve_prefix_witnesses s).1 (twelve_prefix_witnesses s).2 suffix

#print axioms same_shift_all_suffixes
#print axioms twelve_prefix_witnesses
#print axioms twelve_witnesses_preserve_arbitrary_suffix
end ActualPrefixSpecialization
