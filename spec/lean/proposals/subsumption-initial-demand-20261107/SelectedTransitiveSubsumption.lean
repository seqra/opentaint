import Std
import Relations

/-!
PREPARED ONLY. Selected P03/P04 bridge for singleton STAR relations.
Relations.lean is the byte-identical original 49-law model. Here an admitted
NORMAL A supplies a private specialized B which backs diagonal full-mark C.
B is not stored, published or declared admitted. No proper cross-mx law,
static/zero/ND/Target rule, raw-history architecture or native equivalence.
-/
namespace SelectedTransitiveSubsumption
set_option autoImplicit false

inductive Base where
  | zero | staticRoot | register (id : Nat)
  deriving DecidableEq, Repr
inductive Layer where | normal | demand
  deriving DecidableEq, Repr

def baseCode : Base → Nat
  | .zero => 0 | .staticRoot => 1 | .register id => id + 2
def ordinary : Base → Bool
  | .register _ => true | _ => false

/-- These are already-canonical header representations. Native canonical-set
equality is an adapter, not list normalization added by this component.
For cofinite exclusion, the listed marks are the admitted finite complement. -/
inductive Mx where
  | finite (excluded : List Nat)
  | cofinite (admitted : List Nat)
  deriving DecidableEq, Repr
def permits : Mx → Nat → Bool
  | .finite excluded, mark => !(excluded.contains mark)
  | .cofinite admitted, mark => admitted.contains mark

structure Shape where
  owner : Nat
  inputBase : Base
  outputBase : Base
  inputHead : List Nat
  outputHead : List Nat
  inputE : List Nat
  outputE : List Nat
  deriving DecidableEq, Repr
structure Flow where
  shape : Shape
  layer : Layer
  mx : Mx
  admitted : Bool
  deriving DecidableEq, Repr
structure Concrete where
  shape : Shape
  inputMark : Nat
  outputMark : Nat
  layer : Layer
  deriving DecidableEq, Repr

/-- Owner is the exact method/context/direction/scope/ports/stage/catalog key
outside the displayed singleton endpoint geometry. No hash-based equivalence. -/
def relation (shape : Shape) : FlowAntichains.Relations.Row Nat :=
  ⟨shape.owner,baseCode shape.inputBase,baseCode shape.outputBase,
    shape.inputHead,shape.outputHead⟩

def normalDomain (flow : Flow) : Bool :=
  decide (flow.layer = .normal) && ordinary flow.shape.inputBase && ordinary flow.shape.outputBase &&
    decide (flow.shape.inputE = [] ∧ flow.shape.outputE = [])

def specialize (flow : Flow) (suffix : List Nat) : Flow :=
  ⟨⟨flow.shape.owner,flow.shape.inputBase,flow.shape.outputBase,
    flow.shape.inputHead ++ suffix,flow.shape.outputHead ++ suffix,
    flow.shape.inputE,flow.shape.outputE⟩,flow.layer,flow.mx,false⟩

theorem specialized_geometry_is_original_correlated_specialization (flow : Flow) (suffix : List Nat) :
    relation (specialize flow suffix).shape = FlowAntichains.Relations.specialize (relation flow.shape) suffix := rfl
theorem implicit_view_is_not_an_admitted_row (flow : Flow) (suffix : List Nat) :
    (specialize flow suffix).admitted = false := rfl
theorem implicit_view_keeps_mx_and_layer (flow : Flow) (suffix : List Nat) :
    (specialize flow suffix).mx = flow.mx ∧ (specialize flow suffix).layer = flow.layer := ⟨rfl,rfl⟩
theorem implicit_view_keeps_domain (flow : Flow) (suffix : List Nat) :
    normalDomain (specialize flow suffix) = normalDomain flow := rfl

def alignedView (short long : Flow) : Bool :=
  decide (short.admitted = true ∧ normalDomain short = true ∧ normalDomain long = true ∧
    short.mx = long.mx ∧ FlowAntichains.Relations.coversB (relation short.shape) (relation long.shape) = true)
def removeAdmittedLong (short long : Flow) : Bool := alignedView short long && long.admitted

theorem selected_aligned_guard_requires_equal_mx (short long : Flow)
    (covered : alignedView short long = true) : short.mx = long.mx := by
  obtain ⟨_,_,_,equal,_⟩ := of_decide_eq_true covered
  exact equal

theorem proper_cross_mx_aligned_removal_is_rejected (short long : Flow) (different : short.mx ≠ long.mx) :
    alignedView short long = false := by simp [alignedView,different]

theorem selected_equal_mx_aligned_coverage_is_transitive (first middle last : Flow)
    (left : alignedView first middle = true) (right : alignedView middle last = true) :
    alignedView first last = true := by
  obtain ⟨accepted,normal,_,sameLeft,coverLeft⟩ := of_decide_eq_true left
  obtain ⟨_,_,lastNormal,sameRight,coverRight⟩ := of_decide_eq_true right
  have geometry : FlowAntichains.Relations.coversB (relation first.shape) (relation last.shape) = true := by
    apply (FlowAntichains.Relations.coversB_iff _ _).mpr
    exact FlowAntichains.Relations.covers_trans _ _ _
      ((FlowAntichains.Relations.coversB_iff _ _).mp coverLeft)
      ((FlowAntichains.Relations.coversB_iff _ _).mp coverRight)
  apply decide_eq_true
  exact ⟨accepted,normal,lastNormal,sameLeft.trans sameRight,geometry⟩

theorem actual_provider_covers_its_implicit_view (flow : Flow) (suffix : List Nat)
    (accepted : flow.admitted = true) (domain : normalDomain flow = true) :
    alignedView flow (specialize flow suffix) = true := by
  have geometry : FlowAntichains.Relations.coversB (relation flow.shape)
      (relation (specialize flow suffix).shape) = true := by
    rw [specialized_geometry_is_original_correlated_specialization]
    simp [FlowAntichains.Relations.coversB,FlowAntichains.Relations.coverWitness_complete]
  apply decide_eq_true
  exact ⟨accepted,domain,by simpa only [implicit_view_keeps_domain] using domain,rfl,geometry⟩

def concreteGuards (flow : Flow) (marked : Concrete) : Bool :=
  decide (flow.admitted = true ∧ normalDomain flow = true ∧ marked.inputMark = marked.outputMark ∧
    marked.shape.inputE = [] ∧ permits flow.mx marked.outputMark = true)

/-- The one checked suffix is borrowed from A. There is no lookup for B. -/
def concreteView (flow : Flow) (marked : Concrete) : Option Flow :=
  if concreteGuards flow marked then
    (FlowAntichains.Relations.coverWitness (relation flow.shape) (relation marked.shape)).map (specialize flow)
  else none
def coversConcrete (flow : Flow) (marked : Concrete) : Bool := (concreteView flow marked).isSome

def directBacks (view : Flow) (marked : Concrete) : Bool :=
  decide (normalDomain view = true ∧ relation view.shape = relation marked.shape ∧
    marked.inputMark = marked.outputMark ∧ marked.shape.inputE = [] ∧
    permits view.mx marked.outputMark = true)

theorem concrete_view_has_computed_suffix (flow view : Flow) (marked : Concrete)
    (found : concreteView flow marked = some view) :
    concreteGuards flow marked = true ∧ ∃ suffix,
      FlowAntichains.Relations.coverWitness (relation flow.shape) (relation marked.shape) = some suffix ∧
      view = specialize flow suffix := by
  unfold concreteView at found
  split at found
  next guards =>
    cases chosen : FlowAntichains.Relations.coverWitness (relation flow.shape) (relation marked.shape) with
    | none => simp only [chosen,Option.map_none] at found; cases found
    | some suffix =>
      simp only [chosen,Option.map_some,Option.some.injEq] at found
      exact ⟨guards,suffix,rfl,found.symm⟩
  next => cases found

theorem computed_implicit_B_backs_C (flow view : Flow) (marked : Concrete)
    (found : concreteView flow marked = some view) :
    directBacks view marked = true ∧ view.admitted = false ∧ view.mx = flow.mx := by
  obtain ⟨guards,suffix,chosen,same⟩ := concrete_view_has_computed_suffix flow view marked found
  subst view
  have geometry := FlowAntichains.Relations.coverWitness_sound (relation flow.shape) (relation marked.shape) suffix chosen
  obtain ⟨_,normal,diagonal,emptyInput,allowed⟩ := of_decide_eq_true guards
  refine ⟨?_,rfl,rfl⟩
  apply decide_eq_true
  refine ⟨normal,?_,diagonal,emptyInput,?_⟩
  · exact (specialized_geometry_is_original_correlated_specialization flow suffix).trans geometry
  · change permits flow.mx marked.outputMark = true
    exact allowed

theorem aligned_A_and_direct_B_backing_compute_A_cover_without_B_storage
    (first middle : Flow) (marked : Concrete)
    (aligned : alignedView first middle = true) (backed : directBacks middle marked = true) :
    ∃ view, concreteView first marked = some view ∧ view.admitted = false := by
  obtain ⟨accepted,normal,_,sameMx,cover⟩ := of_decide_eq_true aligned
  obtain ⟨_,sameGeometry,diagonal,emptyInput,allowedMiddle⟩ := of_decide_eq_true backed
  have allowed : permits first.mx marked.outputMark = true := by rw [sameMx]; exact allowedMiddle
  have guards : concreteGuards first marked = true := by
    apply decide_eq_true
    exact ⟨accepted,normal,diagonal,emptyInput,allowed⟩
  obtain ⟨suffix,sameMiddle⟩ := (FlowAntichains.Relations.coversB_iff _ _).mp cover
  have sameMarked : FlowAntichains.Relations.specialize (relation first.shape) suffix =
      relation marked.shape := sameMiddle.trans sameGeometry
  have witness : FlowAntichains.Relations.coverWitness (relation first.shape)
      (relation marked.shape) = some suffix := by
    rw [← sameMarked]
    exact FlowAntichains.Relations.coverWitness_complete _ _
  refine ⟨specialize first suffix,?_,rfl⟩
  simp [concreteView,guards,witness]

def flowMeaning (flow : Flow) (pair : FlowAntichains.Relations.Pair Nat) : Prop :=
  permits flow.mx pair.mark = true ∧ FlowAntichains.Relations.denotes (relation flow.shape) pair
def admitsFields : List Nat → List Nat → Prop
  | _,[] => True
  | excluded,field :: _ => field ∉ excluded
def concreteMeaning (marked : Concrete) (pair : FlowAntichains.Relations.Pair Nat) : Prop :=
  pair.mark = marked.inputMark ∧ ∃ suffix,
    FlowAntichains.Relations.produce (relation marked.shape) pair.mark suffix = pair ∧ admitsFields marked.shape.outputE suffix

theorem A_covers_C_without_an_admitted_or_stored_B (flow view : Flow) (marked : Concrete)
    (found : concreteView flow marked = some view) (pair : FlowAntichains.Relations.Pair Nat)
    (member : concreteMeaning marked pair) : flowMeaning flow pair := by
  obtain ⟨guards,suffix,chosen,_⟩ := concrete_view_has_computed_suffix flow view marked found
  obtain ⟨_,_,diagonal,_,allowed⟩ := of_decide_eq_true guards
  obtain ⟨sameMark,rest,pairEq,_⟩ := member
  refine ⟨?_,?_⟩
  · rw [sameMark,diagonal]; exact allowed
  · exact FlowAntichains.Relations.cover_denotation (relation flow.shape) (relation marked.shape)
      ⟨suffix,FlowAntichains.Relations.coverWitness_sound _ _ suffix chosen⟩ pair ⟨rest,pairEq⟩

theorem common_suffix_witness_is_executable (flow : Flow) (outer inner : List Nat) (mark : Nat) :
    FlowAntichains.Relations.produce (relation (specialize flow outer).shape) mark inner =
      FlowAntichains.Relations.produce (relation flow.shape) mark (outer ++ inner) :=
  FlowAntichains.Relations.produced_specialization (relation flow.shape) outer inner mark

theorem excluded_mark_cannot_be_covered (flow : Flow) (marked : Concrete)
    (excluded : permits flow.mx marked.outputMark = false) : concreteView flow marked = none := by
  simp [concreteView,concreteGuards,excluded]
theorem cross_mark_relation_cannot_be_removed (flow : Flow) (marked : Concrete)
    (different : marked.inputMark ≠ marked.outputMark) : concreteView flow marked = none := by
  simp [concreteView,concreteGuards,different]
theorem rejected_A_is_not_a_provider (flow : Flow) (marked : Concrete) (rejected : flow.admitted = false) :
    concreteView flow marked = none := by simp [concreteView,concreteGuards,rejected]

/- Per-complete-C-key executable cell, exactly the old FlowBackedStore rule.
marked is ghost/local processing membership, not a retained raw-summary row.
The runtime-facing residual is the only marked summary queried/published.
flow means an actual accepted coverage witness for THIS key. -/
structure Cell where
  flow : Bool := false
  marked : Bool := false
  blocked : Bool := false
  deriving DecidableEq, Repr
inductive Event where | flow | marked (flag : Bool)
  deriving DecidableEq, Repr
def admitCell (state : Cell) : Event → Cell
  | .flow => ⟨true,state.marked,state.blocked⟩
  | .marked h => ⟨state.flow,true,state.blocked || h⟩
def residual (state : Cell) : Bool := state.marked && (!state.flow || state.blocked)
def novel (state : Cell) (event : Event) : Bool := decide (admitCell state event ≠ state)

theorem cell_admission_commutes (state : Cell) (first second : Event) :
    admitCell (admitCell state first) second = admitCell (admitCell state second) first := by
  cases state with
  | mk flow marked blocked =>
    cases first <;> cases second <;> simp [admitCell,Bool.or_comm,Bool.or_left_comm]
theorem provider_keeps_ordinary_local_membership (state : Cell) :
    (admitCell state .flow).marked = state.marked := rfl
theorem protected_coordinate_is_always_residual (state : Cell) :
    residual (admitCell state (.marked true)) = true := by simp [residual,admitCell]
theorem late_exact_typed_flag_upgrade_is_fresh (state : Cell) (plain : state.blocked = false) :
    novel state (.marked true) = true := by
  cases state with
  | mk flow marked blocked => cases blocked <;> simp_all [novel,admitCell]
theorem repeated_exact_flag_is_not_fresh (state : Cell) :
    novel (admitCell state (.marked true)) (.marked true) = false := by
  cases state with
  | mk flow marked blocked => cases blocked <;> simp [novel,admitCell]

structure State where
  providers : List Flow := []
  cell : Cell := {}
  deriving DecidableEq, Repr
def emptyState : State := ⟨[],{}⟩

/-- Fixed-key oracle for query/index correctness. A-before-C needs no eager
enumeration of C: the native implementation tests the stored A when C arrives. -/
def offerA (marked : Concrete) (state : State) (flow : Flow) : State :=
  if flow.admitted && normalDomain flow then
    ⟨flow :: state.providers,
      if coversConcrete flow marked then admitCell state.cell .flow else state.cell⟩
  else state
def offerC (state : State) (flag : Bool) : State :=
  ⟨state.providers,admitCell state.cell (.marked flag)⟩

theorem C_then_A_and_A_then_C_agree (marked : Concrete) (state : State) (flow : Flow) (h : Bool) :
    offerA marked (offerC state h) flow = offerC (offerA marked state flow) h := by
  unfold offerA offerC
  split
  · split
    · simp only [State.mk.injEq, true_and]
      exact cell_admission_commutes state.cell (.marked h) .flow
    · rfl
  · rfl

theorem source_processing_membership_survives_summary_coverage (marked : Concrete)
    (state : State) (flow : Flow) (h : Bool) :
    (offerA marked (offerC state h) flow).cell.marked = true := by
  unfold offerA offerC
  split
  · split <;> rfl
  · rfl

theorem protected_C_survives_both_orders (marked : Concrete) (state : State) (flow : Flow) :
    residual (offerA marked (offerC state true) flow).cell = true ∧
    residual (offerC (offerA marked state flow) true).cell = true := by
  constructor
  · rw [C_then_A_and_A_then_C_agree]; exact protected_coordinate_is_always_residual _
  · exact protected_coordinate_is_always_residual _

theorem covered_plain_C_is_removed_in_both_orders (marked : Concrete) (flow : Flow)
    (accepted : flow.admitted = true) (domain : normalDomain flow = true)
    (covered : coversConcrete flow marked = true) :
    residual (offerA marked (offerC emptyState false) flow).cell = false ∧
    residual (offerC (offerA marked emptyState flow) false).cell = false := by
  simp [offerA,offerC,accepted,domain,covered,emptyState,residual,admitCell]

theorem a_borrowed_B_cannot_be_registered_as_an_actual_provider (marked : Concrete)
    (state : State) (flow : Flow) (suffix : List Nat) :
    offerA marked state (specialize flow suffix) = state := by
  simp [offerA,specialize]

/- Principal E03 values. B exists only as a transient correlated view. -/
def A : Flow := ⟨⟨42,.register 1,.register 2,[],[],[],[]⟩,.normal,.finite [],true⟩
def B : Flow := specialize A [7]
def C (layer : Layer := .demand) : Concrete :=
  ⟨⟨42,.register 1,.register 2,[7],[7],[],[]⟩,11,11,layer⟩
def CthenA (h : Bool) : State := offerA (C .demand) (offerC emptyState h) A
def AthenC (h : Bool) : State := offerC (offerA (C .demand) emptyState A) h

theorem A_has_a_computed_B_cover_and_B_backs_C :
    alignedView A B = true ∧ concreteView A (C .demand) = some B ∧
    directBacks B (C .demand) = true ∧ B.admitted = false := by decide
theorem C_then_A_removes_plain_C_without_ever_storing_B :
    (CthenA false).providers = [A] ∧ residual (CthenA false).cell = false := by decide
theorem A_then_C_removes_plain_C_without_ever_storing_B :
    (AthenC false).providers = [A] ∧ residual (AthenC false).cell = false := by decide
theorem protected_C_is_kept_in_both_concrete_arrivals :
    residual (CthenA true).cell = true ∧ residual (AthenC true).cell = true := by decide
theorem late_flag_upgrade_wins_after_plain_C_was_compacted :
    residual (offerC (CthenA false) true).cell = true ∧
    novel (CthenA false).cell (.marked true) = true ∧
    (offerC (CthenA false) true).providers = [A] := by decide
theorem ordinary_source_membership_remains_in_both_orders :
    (CthenA false).cell.marked = true ∧ (AthenC false).cell.marked = true := by decide
theorem covering_NORMAL_support_does_not_require_C_to_be_DEMAND :
    coversConcrete A (C .normal) = true ∧ coversConcrete A (C .demand) = true := by decide

def excludedA : Flow := ⟨A.shape,.normal,.finite [11],true⟩
def cofiniteA : Flow := ⟨A.shape,.normal,.cofinite [11],true⟩
def differentMxB : Flow := ⟨B.shape,.normal,.finite [12],true⟩
def wrongOwnerC : Concrete := ⟨⟨43,.register 1,.register 2,[7],[7],[],[]⟩,11,11,.demand⟩
def unalignedC : Concrete := ⟨⟨42,.register 1,.register 2,[7],[],[],[]⟩,11,11,.demand⟩
def wrongMarkC : Concrete := ⟨(C .demand).shape,11,12,.demand⟩
def staticA : Flow := ⟨⟨42,.staticRoot,.register 2,[],[],[],[]⟩,.normal,.finite [],true⟩
def zeroA : Flow := ⟨⟨42,.zero,.register 2,[],[],[],[]⟩,.normal,.finite [],true⟩
def nonemptyEA : Flow := ⟨⟨42,.register 1,.register 2,[],[],[5],[]⟩,.normal,.finite [],true⟩

theorem excluded_T_and_wrong_owner_and_unaligned_rows_are_not_removed :
    coversConcrete excludedA (C .demand) = false ∧
    coversConcrete A wrongOwnerC = false ∧ coversConcrete A unalignedC = false ∧
    coversConcrete A wrongMarkC = false := by decide
theorem cofinite_mx_tests_one_owned_mark_without_enumeration :
    coversConcrete cofiniteA (C .demand) = true ∧ permits (.cofinite [12]) 11 = false := by decide
theorem unequal_canonical_mx_is_not_selected_for_FLOW_to_FLOW_removal :
    alignedView A differentMxB = false := by decide
theorem static_ZERO_nonempty_E_and_unadmitted_providers_are_outside_selected_bridge :
    normalDomain staticA = false ∧ normalDomain zeroA = false ∧ normalDomain nonemptyEA = false ∧
    coversConcrete ⟨A.shape,.normal,A.mx,false⟩ (C .demand) = false := by decide
theorem absent_A_cannot_remove_only_C : residual (offerC emptyState false).cell = true := by decide

end SelectedTransitiveSubsumption
