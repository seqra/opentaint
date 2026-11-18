import RelayTrace
namespace MaskHandoff
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def p : Nat := 0
def ret : Nat := 1
def f : Nat := 1
def t : Nat := 7
def u : Nat := 8
def ap (base : Nat) (path : Path := []) (tail : Tail := .star)
    (mark : Option Nat := none) (mx : List Nat := []) : Ap := ⟨base,path,tail,mark,[],mx⟩
abbrev Edge := Ap × Value

def source : Offered := ⟨ap p [f] .exact (some u),false⟩
def need : Offered := ⟨ap ret [] .exact (some u),false⟩
def start : Seed := ⟨ap p,false⟩

-- The first section deliberately omits F72 demand projection. It proves
-- a failure of that INVALID candidate model, not of the selected analyzer.
-- The final section reinstates the required handoff and rules it out.
-- helper(p) { Box r=p.f; clearT(r); return r; }
-- The cleaner touches this whole head. R31's disjoint branch is inactive.
def clean (v : Value) : Option Value :=
  if v.ap.mark.isNone then some {v with ap:={v.ap with mx:=v.ap.mx++[t]}}
  else if v.ap.mark==some t && v.ap.tail==.exact then none else some v

def read (back : Bool) (v : Value) : Option Value :=
  (if back then BoundedRefinementPipeline.moveE ret p [] [f] v.ap
   else BoundedRefinementPipeline.moveE p ret [f] [] v.ap).map fun w =>
    {w with demand:=w.demand || v.demand,h:=v.h}

def body (back : Bool) (q : Seed) : List Value :=
  let v : Value:=⟨q.ap,q.demand,false⟩
  if back then (clean v >>= read true).toList
  else (read false v >>= clean).toList

def rows1 : List Edge := (body false start).map fun c => (start.ap,c)
def rawRows (edges : List Edge) : List Row := edges.filterMap fun e =>
  if e.2.demand then some ⟨e.2.ap,e.1⟩ else none

def outerStarts : List Seed := (rawRows rows1).flatMap fun row =>
  Run2Relay.emit 2 1 true row.entry need

def innerOffer (q : Seed) : Offered := ⟨q.ap,q.demand⟩
def innerStarts (actual : Offered) : List Seed := (rawRows rows1).flatMap fun row =>
  Run2Relay.emit 2 1 true row.entry actual

def inner2 (actual : Offered) : List Edge := (rawRows rows1).flatMap fun row =>
  (Run2Relay.emit 2 1 true row.entry actual).flatMap fun q =>
    (body true q).filterMap fun c =>
      Run2Relay.restrictOne 2 1 true [actual] q.ap c row

def wrapper2 : List Edge := outerStarts.flatMap fun q => inner2 (innerOffer q)

theorem run1_FLOW_read_produces_intrinsic_MAY_with_the_cleaned_mark_excluded :
    rows1=[(ap p,⟨ap ret [] .may none [t],true,false⟩)] := by decide +kernel

theorem a_nonexcluded_concrete_requirement_starts_a_structural_probe :
    outerStarts=[⟨ap ret [] .exact,false⟩] := by decide +kernel

theorem the_probe_has_lost_the_mask_required_at_the_nested_boundary :
    (outerStarts.map innerOffer)=[⟨ap ret [] .exact,false⟩] ∧
    marksOK (ap ret [] .may none [t]) (ap ret [] .exact)=false := by decide +kernel

theorem the_run2_STAR_repair_is_inactive_in_this_new_cell :
    Run2Relay.cell 2 true (ap ret [] .may none [t]) ⟨ap ret [] .exact,false⟩=false := by decide +kernel

theorem no_inner_or_outer_backward_DATA_reply_is_created :
    innerStarts ⟨ap ret [] .exact,false⟩=[] ∧
    inner2 ⟨ap ret [] .exact,false⟩=[] ∧ wrapper2=[] ∧ rawRows wrapper2=[] := by decide +kernel

theorem rejecting_an_unmasked_FLOW_offer_does_not_depend_on_field_room (k : Nat) :
    Run2Relay.emit 2 k true (ap ret [] .may none [t]) ⟨ap ret [] .exact,false⟩=[] := by
  simp [Run2Relay.emit,Run2Relay.cell,HeadPolicy.emit,CarryPolicy.emit,
    NonEmptyPolicy.emit,emitBase,selector,ap,marksOK,t]

theorem the_concrete_U_point_survives_the_read_and_unrelated_T_cleaner :
    ((read false ⟨source.ap,false,false⟩) >>= clean)=
      some ⟨ap ret [] .exact (some u),false,false⟩ := by decide +kernel

theorem R31_cannot_bypass_the_cleaner_mask_at_this_head :
    DisjointCleaner.safeCone [] [] .exact=false := by decide +kernel

def direct2 : List Edge := inner2 need
def normalBack : Edge := (ap ret,⟨ap p [f] .star none [t],false,false⟩)

theorem a_direct_call_can_learn_the_missing_NORMAL_relation :
    direct2=[normalBack] := by decide +kernel

theorem raw_C5_has_the_concrete_offer_witness_for_that_relation :
    Run2Relay.rawImage 2 1 true (ap ret [] .may none [t]) [need]=[ap ret [] .exact] ∧
    Run2Relay.restrictOne 2 1 true [need] (ap ret [] .exact) normalBack.2
      ⟨ap ret [] .may none [t],ap p⟩=some normalBack := by decide +kernel

-- Keep the unchanged-argument NORMAL record. Its reverse has the same
-- argument base; the root's argument is dead after the call, so the only
-- backward actual is on ret. This NORMAL record cannot start a return route.
def normalArgument : Edge := (ap p,⟨ap p,false,false⟩)
def all1 : List Edge := normalArgument :: rows1

theorem the_unchanged_argument_summary_is_present_but_not_a_return_route :
    rawRows all1=rawRows rows1 ∧ normalArgument.1.base≠need.ap.base := by decide +kernel

-- Grant extra T-only rows from the cleaner request. They still cannot
-- accept U or the unmasked structural probe. No request is disabled.
def tRows : List Row := [⟨ap ret [] .may (some t),ap p [] .star (some t)⟩]
def allRows : List Row := rawRows all1 ++ tRows

theorem even_extra_cleaner_T_rows_cannot_repair_the_masked_U_relay :
    allRows.flatMap (fun row => Run2Relay.emit 2 1 true row.entry need)=outerStarts ∧
    allRows.flatMap (fun row => Run2Relay.emit 2 1 true row.entry ⟨ap ret [] .exact,false⟩)=[] := by decide +kernel

-- Native saved-reversal geometry puts the output mask on the input side.
-- U is admitted, T is not. This is not a predefined relation.
def savedForward (actual : Offered) : Option Offered := do
  if !marksOK (ap p [f] .star none [t]) actual.ap then none else
  let suffix←dropHead [f] actual.ap.path
  some ⟨{actual.ap with base:=ret,path:=suffix},actual.demand⟩

theorem the_NORMAL_service_preserves_U_but_not_the_cleaned_T :
    savedForward source=some need ∧
    savedForward ⟨ap p [f] .exact (some t),false⟩=none := by decide +kernel

theorem the_gap_needs_no_real_field_cut_or_overwrite :
    source.ap.path.length=1 ∧ need.ap.path.length=0 ∧
    rows1.all (fun e => decide (e.1.path.length≤1 ∧ e.2.ap.path.length≤1))=true := by decide +kernel

-- T queries can arise from the cleaner's request. They cannot answer U
-- in this fixed-mark example; a concrete T result cannot become U.
theorem any_concrete_T_demand_rejects_the_U_requirement :
    Run2Relay.emit 2 1 true (ap ret [] .may (some t)) need=[] := by decide +kernel

def missingService : Bool:=wrapper2.isEmpty && (rawRows wrapper2).isEmpty
def later : Nat → Bool
  | 0 => missingService
  | n+1 => later n && missingService

theorem the_unprojected_countermodel_stays_empty_without_a_cutoff (n : Nat) :
    later n=true := by
  induction n with
  | zero => decide +kernel
  | succ n ih => simp [later,ih,missingService,no_inner_or_outer_backward_DATA_reply_is_created,rawRows]

-- Actual AP F72: FLOW demand endpoints have Empty mx. Keep runtime
-- values and saved NORMAL records outside this guidance-only projection.
def demandEndpoint (a : Ap) : Ap := if a.mark.isNone then {a with mx:=[]} else a

def handoff (edges : List Edge) : List Row := (rawRows edges).map fun row =>
  ⟨demandEndpoint row.entry,demandEndpoint row.exit⟩

theorem every_FLOW_demand_endpoint_has_empty_mx (a : Ap) (flow : a.mark=none) :
    (demandEndpoint a).mx=[] := by simp [demandEndpoint,flow]

theorem guidance_projection_preserves_every_other_AP_coordinate (a : Ap) :
    (demandEndpoint a).base=a.base ∧ (demandEndpoint a).path=a.path ∧
    (demandEndpoint a).tail=a.tail ∧ (demandEndpoint a).mark=a.mark ∧
    (demandEndpoint a).e=a.e := by
  unfold demandEndpoint;split <;> simp

theorem concrete_demand_is_not_changed (a : Ap) (mark : a.mark.isSome=true) :
    demandEndpoint a=a := by
  cases h : a.mark <;> simp_all [demandEndpoint]

theorem projection_is_idempotent (a : Ap) :
    demandEndpoint (demandEndpoint a)=demandEndpoint a := by
  unfold demandEndpoint;split <;> simp_all

def actualRows : List Row := handoff all1

theorem the_actual_handoff_is_mask_free_and_keeps_the_own_pair :
    actualRows=[⟨ap ret [] .may,ap p⟩] := by decide +kernel

def actualOuter : List Seed := actualRows.flatMap fun row =>
  Run2Relay.emit 2 1 true row.entry need

def actualInner (actual : Offered) : List Edge := actualRows.flatMap fun row =>
  (Run2Relay.emit 2 1 true row.entry actual).flatMap fun q =>
    (body true q).filterMap fun c =>
      Run2Relay.restrictOne 2 1 true [actual] q.ap c row

theorem the_real_nested_FLOW_probe_is_admitted :
    actualOuter=[⟨ap ret [] .exact,false⟩] ∧
    actualRows.flatMap (fun row => Run2Relay.emit 2 1 true row.entry ⟨ap ret [] .exact,false⟩)=
      [⟨ap ret [] .exact,false⟩] := by decide +kernel

theorem actual_raw_C5_publishes_the_masked_NORMAL_record :
    actualInner ⟨ap ret [] .exact,false⟩=[normalBack] := by decide +kernel

-- Transparent wrappers transport the actual computed reply with their
-- ordinary own-row raw C5. A normalized public key is not the raw start.
def throughWrapper (edges : List Edge) : List Edge := edges.filterMap fun edge =>
  Run2Relay.restrictOne 2 1 true [need] (ap ret [] .exact) edge.2
    ⟨ap ret [] .may,ap p⟩
def actualNested : Nat → List Edge
  | 0 => actualInner ⟨ap ret [] .exact,false⟩
  | n+1 => throughWrapper (actualNested n)

theorem any_finite_wrapper_depth_retains_the_NORMAL_masked_reply (n : Nat) :
    actualNested n=[normalBack] := by
  induction n with
  | zero => exact actual_raw_C5_publishes_the_masked_NORMAL_record
  | succ n ih =>
    change throughWrapper (actualNested n)=[normalBack]
    rw [ih]
    decide +kernel

theorem demand_projection_does_not_erase_the_saved_record_mask :
    normalBack.2.ap.mx=[t] ∧ (demandEndpoint normalBack.2.ap).mx=[] ∧
    normalBack.2.demand=false := by decide +kernel

theorem the_actual_run3_route_retains_U_and_rejects_T :
    actualInner ⟨ap ret [] .exact,false⟩=[normalBack] ∧
    savedForward source=some need ∧
    savedForward ⟨ap p [f] .exact (some t),false⟩=none := by decide +kernel

theorem all_example_paths_fit_the_existing_run2_caps :
    normalBack.1.path.length≤1 ∧ normalBack.2.ap.path.length≤1 ∧
    normalBack.2.ap.path.length≤(ap p).path.length+1 := by decide +kernel

end MaskHandoff
