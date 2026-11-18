import Binding
import Run2Relay
import HeadSafety
import OverwriteReplay

namespace ScalarApplication

open NonEmptyPolicy NonEmptyRestriction

-- Scalar geometry after the ordinary owner, base, mark and role gates.
-- An NE actual has Empty E and always supplies DEMAND support.
structure Residual where
  known : Path
  tail : Tail
  deriving DecidableEq, BEq

def matchNE (actualHead : Path) (premise : Ap) (inside : Bool) : Option Residual :=
  match dropHead premise.path actualHead with
  | some rest =>
    if premise.tail == .star && admits premise.tail premise.e rest
    then some ⟨rest,.ne⟩ else none
  | none =>
    match dropHead actualHead premise.path with
    | some (_ :: _) =>
      if !inside then none
      else if premise.tail == .exact then some ⟨[],.exact⟩
      else if premise.tail == .star then some ⟨[],.may⟩
      else none
    | _ => none

def applyMatched (r : Residual) (output : Value) : Value :=
  let c := {output with demand := true}
  match c.ap.tail with
  | .ne => {c with ap := {c.ap with e := []}}
  | .star => {c with ap := {c.ap with path := c.ap.path ++ r.known, tail := r.tail, e := []}}
  | _ => c

theorem ne_is_an_independent_result_for_every_matched_residual
    (r : Residual) (c : Value) (ne : c.ap.tail = .ne) :
    (applyMatched r c).ap.path = c.ap.path ∧
    (applyMatched r c).ap.tail = .ne ∧ (applyMatched r c).demand = true ∧
    (applyMatched r c).ap.mark = c.ap.mark ∧ (applyMatched r c).h = c.h := by
  simp [applyMatched,ne]

theorem applying_ne_actual_never_upgrades_support (r : Residual) (c : Value) :
    (applyMatched r c).demand = true := by
  cases t : c.ap.tail <;> simp [applyMatched,t]

-- Witness for prefix transport. When the possible suffix q begins with a
-- selected nonempty prefix s, the residual r may be empty.
theorem a_nonempty_prefix_consumes_the_ne_requirement (s r : Path) (nonempty : s ≠ []) :
    admits .ne [] (s ++ r) = true ∧ admits .may [] r = true := by
  cases s with
  | nil => contradiction
  | cons field rest =>
    constructor
    · rfl
    · cases r <;> rfl

theorem empty_residual_is_possible_after_a_strict_descent (f : Nat) :
    admits .ne [] [f] = true ∧ admits .may [] [] = true ∧ admits .ne [] [] = false := by exact ⟨rfl,rfl,rfl⟩

def starP (path : Path := []) (e : List Nat := []) : Ap := ⟨0,path,.star,none,e,[]⟩
def pointP (path : Path := []) : Ap := ⟨0,path,.exact,some 7,[],[]⟩
def result (tail : Tail) : Value := ⟨⟨1,[],tail,some 7,[],[]⟩,false,true⟩

theorem ne_at_the_head_never_supplies_the_exact_point :
    matchNE [] (pointP []) true = none := by decide

theorem a_strict_ne_inside_match_uses_the_selected_ordinary_lane :
    matchNE [] (pointP [1]) true = some ⟨[],.exact⟩ ∧
    matchNE [] (starP [1]) true = some ⟨[],.may⟩ ∧
    matchNE [] (starP [1]) false = none := by decide

theorem a_known_prefix_is_transported_with_its_ne_tail :
    let actual : Offered := ⟨⟨0,[1],.ne,some 7,[],[]⟩,true⟩
    let normal : Ap × Value := (starP [],⟨⟨1,[],.star,none,[],[]⟩,false,false⟩)
    (OverwriteReplay.apply false normal actual).map (fun a => (a.ap.path,a.ap.tail,a.demand)) =
      some ([1],.ne,true) ∧
    matchNE [1] (starP [] [1]) true = none := by decide

theorem a_possible_star_admission_is_demand_even_on_a_normal_offer :
    let offer := BoundedRefinementBinding.rootStar
    let row := BoundedRefinementBinding.child .may
    let starts := BoundedRefinementBinding.uncertainDescent 2 row offer
    starts.length = 2 ∧
      starts.all (fun bind => !BoundedRefinementBinding.canComposeNormalTarget bind offer false) = true := by decide

theorem r08_retains_the_real_head_within_the_global_bound :
    let d : Ap := ⟨0,[],.may,some 7,[],[]⟩
    let a : Offered := ⟨⟨0,[1,2],.must,some 7,[2],[]⟩,false⟩
    let normal := Run2Relay.emit 3 2 false d a
    normal.map (fun q => (q.ap.path,q.ap.e,q.ap.tail,q.demand)) =
      [([1,2],[2],.star,true),([1,2],[2],.star,false),([],[],.exact,false)] ∧
    Run2Relay.emit 3 1 false d a = [] := by decide

theorem every_overrun_in_the_base_family_requires_r08
    (run k : Nat) (back : Bool) (d : Ap) (a : Offered) (q : Seed)
    (member : q ∈ Run2Relay.emit run k back d a)
    (overrun : d.path.length + 1 < q.ap.path.length) :
    ∃ old ∈ CarryPolicy.emit run k back d a,
      HeadPolicy.capException run back d a old = true ∧ q = HeadPolicy.retain a old := by
  cases h : Run2Relay.cell run back d a
  · have admitted : q ∈ HeadPolicy.emit run k back d a := by
      simpa [Run2Relay.emit,h] using member
    exact HeadSafety.every_relative_cap_exception_has_the_enumerated_certificate
      run k back d a q admitted overrun
  · rcases Run2Relay.phase_and_shape_are_the_only_new_branch run back d a h with
      ⟨r,b,_,_,_⟩
    subst run
    subst back
    have bound := (Run2Relay.new_admission_has_no_field_limit_exception k d a q h member).2
    omega

theorem an_r08_premise_does_not_relax_the_paired_output_cap :
    let d : Ap := ⟨0,[],.may,some 7,[],[]⟩
    let a : Offered := ⟨⟨0,[1,2],.must,some 7,[2],[]⟩,false⟩
    let raw : Ap := ⟨0,[1,2],.star,some 7,[2],[]⟩
    let out : Value := ⟨⟨1,[1,2],.exact,some 7,[],[]⟩,false,true⟩
    let row : Row := ⟨d,⟨1,[],.star,some 7,[],[]⟩⟩
    Run2Relay.restrictOne 3 2 false [a] raw out row =
      some (raw,⟨⟨1,[1],.ne,some 7,[],[]⟩,true,true⟩) := by decide

end ScalarApplication
