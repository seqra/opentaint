import Restriction

/- Constructive witness projection for the acyclic program in the report.
   Policy/C5 are imported from the selected non-empty-MAY reference. This
   is not a replacement implementation of the scheduler or the whole IR.
   Extra derivations are allowed: the report checks why the witnesses survive
   the selected compaction rules. No next-run input packet is postulated. -/
namespace AcyclicMayCycle
open NonEmptyPolicy NonEmptyRestriction

local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

instance : ReflBEq Tail where
  rfl := by intro a; cases a <;> rfl
instance : LawfulBEq Tail where
  eq_of_beq := by intro a b h; cases a <;> cases b <;> cases h <;> rfl

local instance : BEq Ap := ⟨fun a b => decide (a = b)⟩
local instance : ReflBEq Ap where
  rfl := by intro a; exact decide_eq_true rfl
local instance : LawfulBEq Ap where
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : BEq Value := ⟨fun a b => decide (a = b)⟩
local instance : ReflBEq Value where
  rfl := by intro a; exact decide_eq_true rfl
local instance : LawfulBEq Value where
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : BEq Seed := ⟨fun a b => decide (a = b)⟩
local instance : ReflBEq Seed where
  rfl := by intro a; exact decide_eq_true rfl
local instance : LawfulBEq Seed where
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
set_option linter.unusedSimpArgs false

def f : Nat := 1
def g : Nat := 2
def p : Nat := 0
def ret : Nat := 1
def t : Nat := 7
def ap (base : Nat) (path : Path) (tail : Tail) (mark : Option Nat := none) : Ap :=
  ⟨base,path,tail,mark,[],[]⟩
def source : Offered := ⟨ap p [f] .must (some t),false⟩
def sinkNeed : Offered := ⟨ap ret [] .may (some t),true⟩
def forwardRow : Row := ⟨ap p [] .may,ap ret [] .star⟩
def backwardRow : Row := ⟨ap ret [] .may,ap p [] .star⟩
def val (a : Ap) (d : Bool := false) : Value := ⟨a,d,false⟩

/-- An ordinary correlated prefix transfer. Unknown STAR/NE reads lose
    correlation; MUST reads are uniform. Known prefixes preserve the tail. -/
def move (fromBase toBase : Nat) (fromPath toPath : Path) (q : Ap) : Option Value :=
  if q.base != fromBase then none
  else match dropHead fromPath q.path with
    | some suffix => some (val {q with base := toBase,path := toPath ++ suffix})
    | none => match dropHead q.path fromPath with
      | some (_ :: _) => match q.tail with
        | .exact => none
        | .must => some (val {q with base := toBase,path := toPath})
        | _ => some (val {q with base := toBase,path := toPath,tail := .may} true)
      | _ => none

/-- Two mutually exclusive return branches, not two serial assignments. -/
def body (backward : Bool) (q : Ap) : List Value :=
  if backward then
    [move ret p [] [f,g] q, move ret p [f] [] q].filterMap id
  else
    [move p ret [f,g] [] q, move p ret [] [f] q].filterMap id

def fresh (run limit : Nat) (backward : Bool) (row : Row)
    (domain : List Offered) (q : Ap) : List (Ap × Value) :=
  (body backward q).filterMap fun c =>
    restrictOne run limit backward domain q (cut limit c) row

def loss (backward : Bool) : Ap × Value :=
  if backward then (ap ret [] .star,val (ap p [] .may) true)
  else (ap p [] .star,val (ap ret [] .may) true)

/-- Ordinary application of an independently-MAY conclusion to an original
    concrete actual. This keeps its mark and D support; it is not an
    admitted-MAY substitute for that actual. Only reached prefix cases. -/
def applyLoss (edge : Ap × Value) (a : Offered) : Option Offered :=
  if edge.1.base != a.ap.base || edge.2.ap.tail != .may || !edge.2.demand then none
  else
    let matched : Bool := match dropHead edge.1.path a.ap.path with
      | some _ => true
      | none => match dropHead a.ap.path edge.1.path with
        | some (_ :: _) => a.ap.tail == .may || a.ap.tail == .must || a.ap.tail == .ne
        | _ => false
    if matched then some ⟨{edge.2.ap with mark := a.ap.mark},true⟩ else none

def bindArgument (a : Offered) : Offered := {a with ap := {a.ap with base := p}}
def bindReturn (a : Offered) : Offered := {a with ap := {a.ap with base := ret}}

theorem actual_source_is_not_a_root_must :
    source.ap.path = [f] ∧ source.ap.tail = .must := by decide

theorem first_call_commands (run k : Nat) :
    emit (run+3) (k+1) false forwardRow.entry source =
      [⟨ap p [f] .star,false⟩,⟨ap p [] .exact,false⟩] := by
  simp [emit,emitBase,completeFamily,primary,atHead,source,forwardRow,
    selector,marksOK,admits,seed,probe,dropHead,ap,legalSeed,f,p,ret] <;> dsimp at * <;> simp

theorem first_call_really_produces_loss :
    val (ap ret [] .may) true ∈ body false (ap p [f] .star) := by decide

theorem partial_loss_is_admitted (run k : Nat) :
    (ap p [f] .star,val (ap ret [] .may) true) ∈
      fresh (run+3) (k+1) false forwardRow [source] (ap p [f] .star) := by
  apply List.mem_filterMap.mpr
  refine ⟨val (ap ret [] .may) true,first_call_really_produces_loss,?_⟩
  unfold restrictOne
  simp only [rawImage,List.flatMap_cons,List.flatMap_nil,first_call_commands]
  simp [forwardRow,normalize,normalAp,intersectExit,selector,marksMeet,cut,ap,val,p,ret]

def partialLoss : Ap × Value := (ap p [f] .star,val (ap ret [] .may) true)
def bOffer : Offered := ⟨ap p [] .may (some t),true⟩

theorem first_call_supplies_the_second_call :
    (applyLoss partialLoss source).map bindArgument = some bOffer := by decide

theorem second_call_commands (run k : Nat) :
    emit (run+3) (k+1) false forwardRow.entry bOffer =
      [⟨ap p [] .exact,false⟩,⟨ap p [] .star,false⟩] := by
  simp [emit,emitBase,completeFamily,primary,atHead,bOffer,forwardRow,
    selector,marksOK,seed,ap,legalSeed,p,ret,dropHead] <;> dsimp at * <;> simp

theorem root_forward_loss_is_admitted (run k : Nat) :
    loss false ∈ fresh (run+3) (k+1) false forwardRow [bOffer] (ap p [] .star) := by
  apply List.mem_filterMap.mpr
  refine ⟨val (ap ret [] .may) true,by decide,?_⟩
  unfold restrictOne
  simp only [rawImage,List.flatMap_cons,List.flatMap_nil,second_call_commands]
  simp [forwardRow,loss,normalize,normalAp,intersectExit,selector,marksMeet,cut,ap,val,p,ret]

theorem root_loss_can_also_replay_at_the_first_call :
    (applyLoss (loss false) source).map bindArgument = some bOffer := by decide

theorem second_call_reaches_the_sink_on_demand :
    applyLoss (loss false) bOffer = some sinkNeed := by decide

theorem backward_commands (run k : Nat) :
    emit (run+2) (k+1) true backwardRow.entry sinkNeed =
      [⟨ap ret [] .exact,false⟩,⟨ap ret [] .star,false⟩] := by
  simp [emit,emitBase,completeFamily,primary,atHead,sinkNeed,backwardRow,
    selector,marksOK,seed,ap,legalSeed,p,ret,dropHead] <;> dsimp at * <;> simp

theorem root_backward_loss_is_admitted (run k : Nat) :
    loss true ∈ fresh (run+2) (k+1) true backwardRow [sinkNeed] (ap ret [] .star) := by
  apply List.mem_filterMap.mpr
  refine ⟨val (ap p [] .may) true,by decide,?_⟩
  unfold restrictOne
  simp only [rawImage,List.flatMap_cons,List.flatMap_nil,backward_commands]
  simp [backwardRow,loss,normalize,normalAp,intersectExit,selector,marksMeet,cut,ap,val,p,ret]

theorem reversed_second_call_supplies_the_first :
    (applyLoss (loss true) sinkNeed).map bindReturn = some sinkNeed := by decide

def sourceHit (a : Offered) : Bool :=
  a.ap.base == p && a.ap.mark == source.ap.mark &&
    (a.ap.tail == .may || a.ap.tail == .must) && a.ap.path.isEmpty

theorem reversed_first_call_reaches_the_real_source :
    ((applyLoss (loss true) sinkNeed).map sourceHit) = some true := by decide

theorem demand_rows_really_reverse :
    (⟨(loss false).2.ap,(loss false).1⟩ : Row) = backwardRow ∧
    (⟨(loss true).2.ap,(loss true).1⟩ : Row) = forwardRow := by decide

theorem witnesses_are_never_cut (k : Nat) :
    cut (k+1) (loss false).2 = (loss false).2 ∧
    cut (k+1) (loss true).2 = (loss true).2 := by
  simp [cut,loss,ap,val]

/-- Native NORMAL return relations of this body, including every suffix
    specialization. Neither return branch relates the root point to itself. -/
def normalReturn (input output : Path) : Prop :=
  input = [f,g] ++ output ∨ output = [f] ++ input

theorem no_normal_root_identity : ¬ normalReturn [] [] := by
  simp [normalReturn,f,g]

theorem independent_may_is_not_covered_by_the_normal_relations :
    ∃ input output : Path, output = [] ∧ ¬ normalReturn input output :=
  ⟨[],[],rfl,no_normal_root_identity⟩

/-- Operational witness projection of a complete run. Extra rows and saved
    NORMAL results are not negative premises of any of these derivations. -/
def forwardCertificate (run limit : Nat) : Bool :=
  let first := fresh run limit false forwardRow [source] (ap p [f] .star)
  if first.contains partialLoss then
    match (applyLoss partialLoss source).map bindArgument with
    | none => false
    | some actual =>
      let queries := emit run limit false forwardRow.entry actual
      queries.any fun q =>
        (fresh run limit false forwardRow [actual] q.ap).contains (loss false) &&
          (applyLoss (loss false) actual).isSome
  else false

def backwardCertificate (run limit : Nat) : Bool :=
  let queries := emit run limit true backwardRow.entry sinkNeed
  queries.any fun q =>
    (fresh run limit true backwardRow [sinkNeed] q.ap).contains (loss true) &&
      (applyLoss (loss true) sinkNeed).any sourceHit

theorem forward_certificate (run k : Nat) : forwardCertificate (run+3) (k+1) = true := by
  unfold forwardCertificate
  dsimp only
  have member := partial_loss_is_admitted run k
  have contained : (fresh (run+3) (k+1) false forwardRow [source]
      (ap p [f] .star)).contains partialLoss = true := by
    exact List.contains_iff_mem.mpr member
  rw [contained]
  simp only [first_call_supplies_the_second_call]
  rw [second_call_commands]
  have root := root_forward_loss_is_admitted run k
  have rootContained := List.contains_iff_mem.mpr root
  simp only [List.any_cons,List.any_nil,Bool.or_false]
  rw [rootContained]
  simp [applyLoss,loss,bOffer,sinkNeed,sourceHit,source,ap,dropHead,val,p,ret,t]

theorem backward_certificate (run k : Nat) : backwardCertificate (run+2) (k+1) = true := by
  unfold backwardCertificate
  rw [backward_commands]
  have root := root_backward_loss_is_admitted run k
  have rootContained := List.contains_iff_mem.mpr root
  simp only [List.any_cons,List.any_nil,Bool.or_false]
  rw [rootContained]
  simp [applyLoss,loss,bOffer,sinkNeed,sourceHit,source,ap,dropHead,val,p,ret,t]

/-- Run-1 uses its selected root STAR abstraction, rather than restricted C2. -/
theorem run1_bootstraps_root_demand :
    val (ap ret [] .may) true ∈ body false (ap p [] .star) ∧
    (applyLoss (loss false) source).map bindArgument = some bOffer ∧
    applyLoss (loss false) bOffer = some sinkNeed := by decide

def fieldLimit (run : Nat) : Nat := if run ≤ 2 then 1 else run-1

/-- True means the DATA witness and root DemandTarget survive at handoff.
    The base is constructed by run1_bootstraps_root_demand. A false state
    does not spontaneously restart. There is no run-limit clause. -/
def forwardHandoffs : Nat → Bool
  | 0 => true
  | n+1 => forwardHandoffs n &&
      backwardCertificate (2*n+2) (2*n+1) &&
      forwardCertificate (2*n+3) (2*n+2)

theorem all_forward_handoffs_keep_the_cycle (n : Nat) : forwardHandoffs n = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [forwardHandoffs,ih,backward_certificate (2*n) (2*n),
      forward_certificate (2*n) (2*n+1)]
    rfl

theorem no_finite_forward_run_has_empty_witness_demand (n : Nat) :
    forwardHandoffs n = true ∧ (loss false).2.demand = true :=
  ⟨all_forward_handoffs_keep_the_cycle n,rfl⟩

theorem each_body_query_is_finite (backward : Bool) (q : Ap) :
    (body backward q).length ≤ 2 := by
  unfold body
  split <;> exact Nat.le_trans (List.length_filterMap_le ..) (by simp)

end AcyclicMayCycle

#print axioms AcyclicMayCycle.first_call_commands
#print axioms AcyclicMayCycle.partial_loss_is_admitted
#print axioms AcyclicMayCycle.first_call_supplies_the_second_call
#print axioms AcyclicMayCycle.second_call_commands
#print axioms AcyclicMayCycle.root_forward_loss_is_admitted
#print axioms AcyclicMayCycle.root_loss_can_also_replay_at_the_first_call
#print axioms AcyclicMayCycle.second_call_reaches_the_sink_on_demand
#print axioms AcyclicMayCycle.backward_commands
#print axioms AcyclicMayCycle.root_backward_loss_is_admitted
#print axioms AcyclicMayCycle.reversed_second_call_supplies_the_first
#print axioms AcyclicMayCycle.reversed_first_call_reaches_the_real_source
#print axioms AcyclicMayCycle.demand_rows_really_reverse
#print axioms AcyclicMayCycle.witnesses_are_never_cut
#print axioms AcyclicMayCycle.no_normal_root_identity
#print axioms AcyclicMayCycle.independent_may_is_not_covered_by_the_normal_relations
#print axioms AcyclicMayCycle.forward_certificate
#print axioms AcyclicMayCycle.backward_certificate
#print axioms AcyclicMayCycle.run1_bootstraps_root_demand
#print axioms AcyclicMayCycle.all_forward_handoffs_keep_the_cycle
#print axioms AcyclicMayCycle.no_finite_forward_run_has_empty_witness_demand
#print axioms AcyclicMayCycle.each_body_query_is_finite
