import Std
namespace DemandDataAncestry
/- Necessary typed gates only. They do not claim AP geometry acceptance or
   global run-1 coverage. In later runs there is no static completion/carry. -/
inductive Entry where | data | zero | target deriving DecidableEq, Repr
inductive Exit where | data | zero deriving DecidableEq, Repr
inductive Original where | data | zero deriving DecidableEq, Repr
structure Pair where
  entry : Entry
  output : Exit
  deriving DecidableEq, Repr
inductive Origin where
  | dataSummary (premise : Original)
  | zeroSummary (premise : Original)
  | demandTarget (premise : Original)
  deriving DecidableEq, Repr

def projected : Origin → Pair
  | .dataSummary .data => ⟨.data,.data⟩
  | .dataSummary .zero => ⟨.data,.zero⟩
  | .zeroSummary .data => ⟨.zero,.data⟩
  | .zeroSummary .zero => ⟨.zero,.zero⟩
  | .demandTarget .data => ⟨.target,.data⟩
  | .demandTarget .zero => ⟨.target,.zero⟩

def canStartData (p : Pair) : Bool := match p.entry with | .data => true | _ => false
def canStartZero (p : Pair) : Bool := match p.entry with | .data => false | _ => true
def entryKindAdmits (p : Pair) (j : Original) : Bool := match j with
  | .data => canStartData p
  | .zero => canStartZero p
def canPublishData (p : Pair) (j : Original) : Bool :=
  entryKindAdmits p j && (match p.output with | .data => true | .zero => false)

theorem nonzero_start_needs_data_entry (p : Pair) (h : canStartData p = true) :
    p.entry = .data := by
  cases p with
  | mk entry output => cases entry <;> simp_all [canStartData]
theorem target_cannot_start_data (e : Exit) :
    canStartData ⟨.target,e⟩ = false := by rfl
theorem zero_entry_cannot_start_data (e : Exit) :
    canStartData ⟨.zero,e⟩ = false := by rfl
theorem projected_data_entry_has_data_producer (o : Origin)
    (h : canStartData (projected o) = true) :
    ∃ j, o = .dataSummary j := by
  cases o with
  | dataSummary j => exact ⟨j,rfl⟩
  | demandTarget j => cases j <;> contradiction
  | zeroSummary j => cases j <;> contradiction

theorem zero_summary_cannot_start_data (j : Original) :
    canStartData (projected (.zeroSummary j)) = false := by cases j <;> rfl

theorem data_publication_needs_data_exit (p : Pair) (j : Original)
    (h : canPublishData p j = true) : p.output = .data := by
  cases p with
  | mk entry output => cases output <;> simp_all [canPublishData]
theorem target_data_starts_zero : canStartZero (projected (.demandTarget .data)) = true := by decide
theorem target_data_can_publish_zero_data :
    canPublishData (projected (.demandTarget .data)) .zero = true := by decide
theorem target_zero_cannot_publish_data (j : Original) :
    canPublishData (projected (.demandTarget .zero)) j = false := by cases j <;> decide

def allPureControl (rows : List Pair) : Bool := rows.all fun p =>
  !canStartData p && !(p.output == .data)
def anyDataStart (rows : List Pair) : Bool := rows.any canStartData
private theorem checked_member {rows : List Pair} {p : Pair}
    (h : allPureControl rows = true) (hp : p ∈ rows) : canStartData p = false := by
  have each := List.all_eq_true.mp h p hp
  cases hd : canStartData p <;> simp_all

theorem pure_control_has_no_data_start (rows : List Pair)
    (h : allPureControl rows = true) : anyDataStart rows = false := by
  unfold anyDataStart
  cases answer : rows.any canStartData with
  | false => rfl
  | true =>
    obtain ⟨p,hp,hyes⟩ := List.any_eq_true.mp answer
    have no := checked_member h hp
    rw [no] at hyes
    contradiction

/- These are real typed countercontrols to invalid ancestry shortcuts. -/
theorem data_entry_does_not_imply_nonzero_prior_premise :
    canStartData (projected (.dataSummary .zero)) = true := by decide
theorem target_data_has_no_data_entry_but_has_data_exit :
    canStartData (projected (.demandTarget .data)) = false ∧
    canPublishData (projected (.demandTarget .data)) .zero = true := by decide

structure Scope where
  owner : Nat
  block : Nat
  inputPort : Nat
  outputPort : Nat
  deriving DecidableEq, Repr

def flip (s : Scope) : Scope := ⟨s.owner,s.block,s.outputPort,s.inputPort⟩
theorem scope_flip_is_involution (s : Scope) : flip (flip s) = s := by cases s; rfl
theorem scope_flip_keeps_owner_and_block (s : Scope) :
    (flip s).owner = s.owner ∧ (flip s).block = s.block := ⟨rfl,rfl⟩
end DemandDataAncestry
#print axioms DemandDataAncestry.nonzero_start_needs_data_entry
#print axioms DemandDataAncestry.target_cannot_start_data
#print axioms DemandDataAncestry.zero_entry_cannot_start_data
#print axioms DemandDataAncestry.projected_data_entry_has_data_producer
#print axioms DemandDataAncestry.zero_summary_cannot_start_data
#print axioms DemandDataAncestry.data_publication_needs_data_exit
#print axioms DemandDataAncestry.target_data_starts_zero
#print axioms DemandDataAncestry.target_data_can_publish_zero_data
#print axioms DemandDataAncestry.target_zero_cannot_publish_data
#print axioms DemandDataAncestry.pure_control_has_no_data_start
#print axioms DemandDataAncestry.data_entry_does_not_imply_nonzero_prior_premise
#print axioms DemandDataAncestry.target_data_has_no_data_entry_but_has_data_exit
#print axioms DemandDataAncestry.scope_flip_is_involution
#print axioms DemandDataAncestry.scope_flip_keeps_owner_and_block
