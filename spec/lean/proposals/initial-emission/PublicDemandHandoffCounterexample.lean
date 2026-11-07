/-
Local public-handoff counterexample; no repair is selected here.
Use the checked new C2/normalizer. Raw singleton concrete DATA P/C use SOA,
DEMAND and Empty E. Public normalization erases SOA. Backward-to-forward
handoff reverses C/P into demand entry/exit; layer D selects this row.
Next run3 has an ordinary child EXACT/T NORMAL actual. STAR demand rejects it;
the old MAY demand admits terminal child EXACT/T NORMAL. All paths fit budget.
This is a next-C2 image difference, not a whole-program/global soundness proof.
-/
import StarOrAnyDesignProofFixed

namespace StarOrAnyPublicHandoff
open ApSpec StarOrAnyDesign
abbrev Mark := StarOrAnyDesign.Mark
abbrev Pattern := StarOrAnyDesign.Pattern
abbrev Fact := StarOrAnyDesign.Fact
abbrev Seed := StarOrAnyDesign.Seed
abbrev Demand := StarOrAnyDesign.Demand

/-- Base1 is the argument; base2 is the return. These are symbolic ordinary
bases, not recorded Java variables, physical ports or injected runtime rows. -/
def argumentSOA : Pattern := ⟨1,[],.starOrAny,T,[]⟩
def returnSOA : Pattern := ⟨2,[],.starOrAny,T,[]⟩
def argumentSTAR : Pattern := erase argumentSOA
def returnSTAR : Pattern := erase returnSOA
def argumentMAY : Pattern := ⟨1,[],.plain .may,T,[]⟩
def returnMAY : Pattern := ⟨2,[],.plain .may,T,[]⟩
def rawSOARow : PublicRow := ⟨[returnSOA],.data ⟨argumentSOA,.demand,false⟩⟩
def normalizedSOARow : PublicRow := normalizePublic rawSOARow
def oldMAYRow : PublicRow := ⟨[returnMAY],.data ⟨argumentMAY,.demand,false⟩⟩
def childEXACT : Fact := ⟨⟨1,[f],.plain .exact,T,[]⟩,.normal,false⟩
def childSeed : Seed := ⟨childEXACT.pattern,.normal⟩
def rootSTAR : Demand := ⟨1,[],.star,T⟩
def rootMAY : Demand := ⟨1,[],.any,T⟩

structure Pair where
  entry : Pattern
  exit : Pattern
deriving DecidableEq, Repr

/-- Singleton concrete DATA case of backward HandOff.toForward. D is sufficient
for selectedForHandoff. Other selectors/ND/control/static/ownership are open. -/
def backwardHandoff (row : PublicRow) : List Pair :=
  match row.premises,row.payload with
  | [p],.data conclusion => if conclusion.layer = .demand then [⟨conclusion.pattern,p⟩] else []
  | _,_ => []
def asC2Demand (p : Pattern) : Demand :=
  let geometric := scalar p
  ⟨geometric.base,geometric.path,geometric.shape,geometric.mark⟩
def handoffAdmissions (run : Nat) (row : PublicRow) (actual : Fact) : List Seed :=
  (backwardHandoff row).flatMap fun pair => c2 .starThenMayForAny run mode (asC2Demand pair.entry) actual

theorem public_normalization_erases_both_concrete_slots_but_keeps_DEMAND :
    normalizedSOARow = ⟨[returnSTAR],.data ⟨argumentSTAR,.demand,false⟩⟩ ∧
    scalar argumentSOA = scalar argumentSTAR ∧
    (normalizePublic rawSOARow).premises = [returnSTAR] := by decide

theorem selected_backward_handoff_retains_the_STAR_entry_and_paired_exit :
    backwardHandoff normalizedSOARow = [⟨argumentSTAR,returnSTAR⟩] ∧
    asC2Demand argumentSTAR = rootSTAR ∧
    backwardHandoff oldMAYRow = [⟨argumentMAY,returnMAY⟩] ∧
    asC2Demand argumentMAY = rootMAY := by decide

theorem ordinary_run3_STAR_demand_rejects_child_EXACT_while_MAY_admits_it :
    c2 .starThenMayForAny 3 mode rootSTAR childEXACT = [] ∧
    c2 .starThenMayForAny 3 mode rootMAY childEXACT = [childSeed] ∧
    RestrictedInitialPolicy.emit rootSTAR (scalar childEXACT.pattern) = none ∧
    RestrictedInitialPolicy.emit rootMAY (scalar childEXACT.pattern) =
      some (scalar childEXACT.pattern) := by decide

theorem normalized_public_handoff_changes_the_next_joint_admission_image :
    handoffAdmissions 3 normalizedSOARow childEXACT = [] ∧
    handoffAdmissions 3 oldMAYRow childEXACT = [childSeed] := by decide

theorem new_concrete_initial_stays_DEMAND_before_public_erasure :
    c2 .starThenMayForAny 3 mode rootMAY ⟨argumentMAY,.demand,false⟩ =
      [⟨argumentSOA,.demand⟩] ∧
    eraseSeed ⟨argumentSOA,.demand⟩ = ⟨argumentSTAR,.demand⟩ := by decide

theorem same_head_and_run2_controls_do_not_repair_the_run3_descendant_cell :
    c2 .starThenMayForAny 3 mode rootSTAR
      ⟨⟨1,[],.plain .exact,T,[]⟩,.normal,false⟩ =
      [⟨⟨1,[],.plain .exact,T,[]⟩,.normal⟩] ∧
    c2 .starThenMayForAny 2 ⟨.backward,2⟩ rootSTAR childEXACT =
      [⟨argumentSTAR,.demand⟩] ∧
    c2 .starThenMayForAny 3 mode rootSTAR childEXACT = [] := by decide

theorem the_lost_next_admission_has_an_explicit_ordinary_actual_witness :
    ∃ actual : Fact, actual = childEXACT ∧
      handoffAdmissions 3 oldMAYRow actual = [childSeed] ∧
      handoffAdmissions 3 normalizedSOARow actual = [] := by
  exact ⟨childEXACT,rfl,by decide,by decide⟩

def check : Bool :=
  decide (handoffAdmissions 3 normalizedSOARow childEXACT = []) &&
  decide (handoffAdmissions 3 oldMAYRow childEXACT = [childSeed]) &&
  decide (childEXACT.layer = .normal) &&
  decide (childEXACT.pattern.path.length ≤ mode.fieldLimit) &&
  decide (asC2Demand argumentSTAR = rootSTAR)

theorem executable_handoff_counterexample : check = true := by decide
#eval (if check then "SOA_PUBLIC_HANDOFF_COUNTEREXAMPLE=true" else "SOA_PUBLIC_HANDOFF_COUNTEREXAMPLE=false")

#print axioms public_normalization_erases_both_concrete_slots_but_keeps_DEMAND
#print axioms selected_backward_handoff_retains_the_STAR_entry_and_paired_exit
#print axioms ordinary_run3_STAR_demand_rejects_child_EXACT_while_MAY_admits_it
#print axioms normalized_public_handoff_changes_the_next_joint_admission_image
#print axioms new_concrete_initial_stays_DEMAND_before_public_erasure
#print axioms same_head_and_run2_controls_do_not_repair_the_run3_descendant_cell
#print axioms the_lost_next_admission_has_an_explicit_ordinary_actual_witness
#print axioms executable_handoff_counterexample

end StarOrAnyPublicHandoff
