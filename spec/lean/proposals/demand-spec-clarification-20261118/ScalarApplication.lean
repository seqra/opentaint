import Binding
import Run2Relay
import HeadSafety
import OverwriteReplay
import PointWriteReplay

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

def mayDemand : Ap := ⟨0,[],.may,some 7,[],[]⟩
def mustActual (path e : Path) (demand : Bool := false) : Offered :=
  ⟨⟨0,path,.must,some 7,e,[]⟩,demand⟩
def starred (path e : Path) (mark : Option Nat) : Seed :=
  ⟨⟨0,path,.star,mark,e,[]⟩,mark.isSome⟩
def shortFamily : List Seed :=
  [starred [1] [] (some 7),starred [1] [] none,probe mayDemand]

theorem r07_keeps_the_head_and_prefix_probe_in_the_full_family :
    let actual := mustActual [1] [4]
    Run2Relay.emit 5 4 false mayDemand actual =
      [starred [1] [4] (some 7),starred [1] [4] none,probe mayDemand] := by decide

theorem r07_leaves_the_three_field_offer_short_and_r08_moves_both_stars :
    let actual := mustActual [1,2,3] [4]
    CarryPolicy.emit 5 4 false mayDemand actual = shortFamily ∧
    Run2Relay.emit 5 4 false mayDemand actual =
      [starred [1,2,3] [4] (some 7),starred [1,2,3] [4] none,probe mayDemand] := by decide

theorem r08_three_field_controls_keep_the_short_family :
    Run2Relay.emit 5 4 false mayDemand (mustActual [1,2,3] []) = shortFamily ∧
    Run2Relay.emit 5 4 false mayDemand (mustActual [1,2,3] [4] true) = shortFamily ∧
    Run2Relay.emit 5 4 false {mayDemand with mark := none} (mustActual [1,2,3] [4]) =
      [starred [1] [] none,probe mayDemand] ∧
    Run2Relay.emit 5 2 false mayDemand (mustActual [1,2,3] [4]) = [] := by decide

theorem the_ne_selector_keeps_only_the_two_deeper_star_commands :
    Run2Relay.emit 5 4 false {mayDemand with tail := .ne} (mustActual [1,2,3] [4]) =
      [starred [1,2,3] [4] (some 7),starred [1,2,3] [4] none] := by decide

theorem the_three_field_r08_publication_has_one_output_field :
    let actual := mustActual [1,2,3] [4]
    let raw := (starred [1,2,3] [4] (some 7)).ap
    let output : Value := ⟨⟨1,[1,2,3],.exact,some 7,[],[]⟩,true,false⟩
    let row : Row := ⟨mayDemand,⟨1,[],.star,some 7,[],[]⟩⟩
    Run2Relay.restrictOne 5 4 false [actual] raw output row =
      some (raw,⟨⟨1,[1],.ne,some 7,[],[]⟩,true,false⟩) := by decide

theorem r13_keeps_the_excluded_point_and_removes_the_child_result :
    let actual : Value := ⟨⟨0,[],.exact,none,[],[]⟩,false,false⟩
    let expected : Value := ⟨⟨0,[],.exact,none,[1],[]⟩,false,false⟩
    let child : Value := ⟨⟨0,[1],.may,none,[],[]⟩,true,false⟩
    NestedWriteReplay.keep 5 [] 1 actual = some expected ∧
    PointWriteReplay.keep 5 [] 1 actual = some expected ∧
    NestedWriteReplay.keep 5 [1] 2 actual = some child ∧
    PointWriteReplay.keep 5 [1] 2 actual = none ∧
    OverwriteReplay.move [1] [] expected.ap = none := by decide

theorem the_c5_point_and_star_examples_publish_different_sets_under_ne :
    let entry : Ap := ⟨0,[],.may,none,[],[]⟩
    let exit : Ap := ⟨1,[],.star,none,[],[]⟩
    let row : Row := ⟨entry,exit⟩
    let neRow : Row := ⟨{entry with tail := .ne},exit⟩
    let actual : Offered := ⟨entry,true⟩
    let point : Ap := {entry with tail := .exact}
    let star : Ap := {entry with tail := .star}
    let rawPoint : Value := ⟨{exit with tail := .exact, e := [1]},false,false⟩
    let output : Value := ⟨{exit with e := [1]},false,false⟩
    Run2Relay.restrictOne 5 4 false [actual] point rawPoint row = some (star,output) ∧
    Run2Relay.restrictOne 5 4 false [actual] point rawPoint neRow = none ∧
    Run2Relay.restrictOne 5 4 false [actual] star output neRow = some (star,output) := by decide

theorem the_c5_companion_uses_the_same_rows_conclusion_and_mark :
    let exit : Ap := ⟨1,[],.exact,some 7,[],[]⟩
    let row : Row := ⟨mayDemand,exit⟩
    let actual : Offered := ⟨mayDemand,true⟩
    let companion : Ap := starP []
    let old : Value := ⟨⟨1,[],.may,none,[],[]⟩,true,false⟩
    let cut : Value := {old with ap := {old.ap with tail := .ne}}
    let published : Value := {old with ap := {old.ap with tail := .star}}
    Run2Relay.restrictOne 5 4 false [actual] companion old row = some (companion,published) ∧
    Run2Relay.restrictOne 5 4 false [actual] companion cut row = none := by decide

end ScalarApplication
