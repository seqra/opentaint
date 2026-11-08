/-
Selected ordinary-AP C2/C5 component. Arbitrary Nat bases, Nat field lists,
FLOW/full Nat marks, finite field exclusions, restricted runs >= 2, FULL.
Every path accessor is counted. Demand MAY and concrete EXACT have Empty E.
FLOW STAR demand E is ignored; concrete STAR demand E is retained.

STAR is an identity start, never an independent-continuation MAY start.
Concrete STAR seeds are DEMAND. No companion FLOW admission is added.
No STAR-to-MAY handoff, new tail, static-anchor adapter or driver theorem.

Only baseline-identical RestrictedInitialPolicy is imported for path helpers
and scalar mark matching. No withdrawn STAR/SOA prototype is imported.
-/
import RestrictedInitialPolicy

namespace PlainStarRelativeAdmission
open ApSpec
abbrev ScalarMark := RestrictedInitialPolicy.Mark
abbrev Shape := RestrictedInitialPolicy.Shape

inductive Tail where | exact | star | any | must
deriving DecidableEq, Repr
inductive Layer where | normal | demand
deriving DecidableEq, Repr
inductive Direction where | forward | backward
deriving DecidableEq, Repr

structure Mode where
  run : Nat
  limit : Nat
  direction : Direction
deriving DecidableEq, Repr

structure Demand where
  base : Nat
  path : List Nat
  shape : Shape
  mark : ScalarMark
  exclusion : List Nat
deriving DecidableEq, Repr

structure Pattern where
  base : Nat
  path : List Nat
  tail : Tail
  mark : ScalarMark
  exclusion : List Nat
deriving DecidableEq, Repr

structure Actual where
  pattern : Pattern
  layer : Layer
  hasProtection : Bool := false
deriving DecidableEq, Repr

structure Seed where
  initial : Pattern
  layer : Layer
deriving DecidableEq, Repr

def joinLayer : Layer → Layer → Layer
  | .normal, .normal => .normal
  | _, _ => .demand

def intrinsic (p : Pattern) : Layer :=
  match p.tail, p.mark with
  | .any, _ | .star, .full _ => .demand
  | _, _ => .normal

def demandE (d : Demand) : List Nat :=
  match d.shape, d.mark with
  | .star, .flow => []
  | _, _ => d.exclusion

def validDemand (d : Demand) : Prop :=
  match d.shape, d.mark with
  | .any, _ | .exact, .full _ => d.exclusion = []
  | _, _ => True

instance (d : Demand) : Decidable (validDemand d) := by
  unfold validDemand
  cases d.shape <;> cases d.mark <;> infer_instance

def legalActual (mode : Mode) (a : Actual) : Prop :=
  a.pattern.path.length ≤ mode.limit ∧
  match a.pattern.tail, a.pattern.mark with
  | .exact, _ => a.pattern.exclusion = []
  | .any, _ => a.pattern.exclusion = [] ∧ a.layer = .demand
  | .star, .full _ => a.layer = .demand
  | _, _ => True

instance (mode : Mode) (a : Actual) : Decidable (legalActual mode a) := by
  unfold legalActual
  cases a.pattern.tail <;> cases a.pattern.mark <;> infer_instance

def concrete : ScalarMark → Bool
  | .full _ => true
  | .flow => false

def tailAdmits (tail : Tail) (e : List Nat) (rest : List Nat) : Bool :=
  match tail with
  | .exact => rest.isEmpty
  | .any => true
  | .star | .must => (Excl.set e).admits rest

def demandAdmits (d : Demand) (rest : List Nat) : Bool :=
  match d.shape with
  | .any => true
  | .exact => rest.isEmpty
  | .star => (Excl.set (demandE d)).admits rest

inductive Template where
  | rootExact
  | rootStar
  | rootMust (exclusion : List Nat)
  | childStar (field : Nat)
  | childExact (field : Nat)
deriving DecidableEq, Repr

def starE (d : Demand) : List Nat :=
  match d.shape with | .star => demandE d | _ => []

def render (d : Demand) : Template → Pattern
  | .rootExact => ⟨d.base,d.path,.exact,d.mark,[]⟩
  | .rootStar => ⟨d.base,d.path,.star,d.mark,starE d⟩
  | .rootMust e => ⟨d.base,d.path,.must,d.mark,e⟩
  | .childStar f => ⟨d.base,d.path ++ [f],.star,d.mark,[]⟩
  | .childExact f => ⟨d.base,d.path ++ [f],.exact,d.mark,[]⟩

/- This is a finite descriptor-domain check, including the existing output
budget and backward-MUST guard. It is not an enumeration of actual inputs. -/
def Allowed (mode : Mode) (d : Demand) (t : Template) : Prop :=
  mode.run ≥ 2 ∧ mode.limit ≥ 1 ∧ validDemand d ∧ d.path.length ≤ mode.limit ∧
  match t with
  | .rootExact => True
  | .rootStar => d.shape = .any ∨
      (d.shape = .star ∧ mode.run = 2 ∧ d.path.length < mode.limit)
  | .rootMust _ => d.shape = .any ∧ mode.direction = .forward
  | .childStar _ => d.shape = .any ∧ d.path.length + 1 ≤ mode.limit
  | .childExact _ => d.shape = .any ∧ concrete d.mark = true ∧
      d.path.length + 1 ≤ mode.limit

instance (mode : Mode) (d : Demand) (t : Template) : Decidable (Allowed mode d t) := by
  unfold Allowed
  cases t <;> infer_instance

def commonLegal (mode : Mode) (d : Demand) (a : Actual) : Prop :=
  mode.run ≥ 2 ∧ mode.limit ≥ 1 ∧ validDemand d ∧
  d.path.length ≤ mode.limit ∧ legalActual mode a ∧
  d.base = a.pattern.base ∧
  RestrictedInitialPolicy.acceptsMark d.mark a.pattern.mark = true ∧
  ¬ (d.shape = .exact ∧ d.mark = .flow ∧ a.pattern.tail = .any)

instance (mode : Mode) (d : Demand) (a : Actual) : Decidable (commonLegal mode d a) := by
  unfold commonLegal
  infer_instance

/- Ordinary C2 table, with only selected ANY-result -> STAR changes and the
new same-head ANY demand + STAR actual cell. The later STAR descendant row
still rejects. Original actual E gates every ancestor-to-demand descent. -/
def table (mode : Mode) (d : Demand) (a : Actual) : Option Template :=
  if commonLegal mode d a then
    match d.shape, relate d.path a.pattern.path with
    | .any, .below [] =>
      match a.pattern.tail with
      | .exact => some .rootExact
      | .star | .any => some .rootStar
      | .must => some (.rootMust a.pattern.exclusion)
    | .any, .below (f :: rest) =>
      if concrete d.mark && decide (a.pattern.tail = .exact) && rest.isEmpty
      then some (.childExact f) else some (.childStar f)
    | .star, .below (f :: rest) =>
      if demandAdmits d (f :: rest) && decide (mode.run = 2)
      then some .rootStar else none
    | .exact, .below (_ :: _) => none
    | .any, .above rest =>
      if tailAdmits a.pattern.tail a.pattern.exclusion rest then
        match a.pattern.tail with
        | .any => some .rootStar
        | .must => some (.rootMust (demandE d))
        | _ => none
      else none
    | _, .above rest =>
      if tailAdmits a.pattern.tail a.pattern.exclusion rest
      then some .rootExact else none
    | _, .below [] => some .rootExact
    | _, .apart => none
  else none

def selected (mode : Mode) (d : Demand) (a : Actual) : Option Template :=
  match table mode d a with
  | none => none
  | some t => if Allowed mode d t then some t else none

def admissionLayer (initial : Pattern) (a : Actual) : Layer :=
  match initial.mark with
  | .flow => intrinsic initial
  | .full _ => joinLayer (intrinsic initial)
      (joinLayer a.layer
        (if initial.tail = .exact ∧ a.pattern.tail = .any then .demand else .normal))

def emit (mode : Mode) (d : Demand) (a : Actual) : Option Seed :=
  (selected mode d a).map fun t =>
    let initial := render d t
    ⟨initial,admissionLayer initial a⟩

/- STAR starts itself with correlated identity continuation. H is supplied
by a producer/transfer, not created by this start. -/
def start (seed : Seed) : Actual :=
  ⟨seed.initial,joinLayer (intrinsic seed.initial) seed.layer,false⟩

def maxField : List Nat → Nat
  | [] => 0
  | f :: rest => max f (maxField rest)

def freshField (e : List Nat) : Nat := maxField e + 1

theorem member_bounded_by_maxField (e : List Nat) (f : Nat) (member : f ∈ e) :
    f ≤ maxField e := by
  induction e with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst f; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

theorem freshField_not_member (e : List Nat) : freshField e ∉ e := by
  intro member
  have bounded := member_bounded_by_maxField e (freshField e) member
  unfold freshField at bounded
  omega

theorem freshField_is_admitted (e : List Nat) :
    (Excl.set e).admits [freshField e] = true := by
  have absent : memB (freshField e) e = false := by
    cases found : memB (freshField e) e with
    | false => rfl
    | true => exact False.elim (freshField_not_member e (CoreAux.memB_iff.mp found))
  simp [Excl.admits,absent]

def templateActual (d : Demand) (t : Template) : Actual :=
  match t with
  | .rootStar =>
      if d.shape = .star then
        ⟨⟨d.base,d.path ++ [freshField (demandE d)],.exact,d.mark,[]⟩,.normal,false⟩
      else ⟨render d t,intrinsic (render d t),false⟩
  | _ => ⟨render d t,intrinsic (render d t),false⟩

theorem selected_is_allowed (mode : Mode) (d : Demand) (a : Actual) (t : Template)
    (found : selected mode d a = some t) : Allowed mode d t := by
  unfold selected at found
  cases chosen : table mode d a with
  | none => simp [chosen] at found
  | some candidate =>
    rw [chosen] at found
    by_cases valid : Allowed mode d candidate
    · simp only [if_pos valid,Option.some.injEq] at found
      exact found ▸ valid
    · simp [valid] at found

theorem same_path_relation (path : List Nat) : relate path path = .below [] := by
  simp [relate,ApSpec.Handoff.RAux.dropPrefix_self']

theorem one_child_relation (path : List Nat) (f : Nat) :
    relate path (path ++ [f]) = .below [f] := by
  have prefixPath : dropPrefix path (path ++ [f]) = some [f] :=
    CoreAux.dropPrefix_some.mpr rfl
  simp [relate,prefixPath]

/- This theorem is constructive for arbitrary paths, marks and finite E.
The only requested-STAR witness is a fresh counted EXACT child, not the
initial itself; its actual layer is NORMAL. Concrete STAR self-witnesses
instead use intrinsic DEMAND, never an impossible NORMAL STAR/T payload. -/
theorem allowed_template_has_legal_executable_witness
    (mode : Mode) (d : Demand) (t : Template) (allowed : Allowed mode d t) :
    legalActual mode (templateActual d t) ∧
    emit mode d (templateActual d t) =
      some ⟨render d t,intrinsic (render d t)⟩ := by
  rcases d with ⟨base,path,shape,mark,e⟩
  cases t with
  | rootExact =>
    rcases allowed with ⟨run,limit,valid,fits,cell⟩
    cases shape <;> cases mark <;>
      simp_all [templateActual,render,intrinsic,legalActual,emit,selected,table,
        commonLegal,Allowed,validDemand,admissionLayer,joinLayer,
        same_path_relation,RestrictedInitialPolicy.acceptsMark]
  | rootMust excluded =>
    rcases allowed with ⟨run,limit,valid,fits,shapeIs,directionIs⟩
    change shape = .any at shapeIs
    subst shape
    cases mark <;>
      simp_all [templateActual,render,intrinsic,legalActual,emit,selected,table,
        commonLegal,Allowed,admissionLayer,joinLayer,same_path_relation,
        RestrictedInitialPolicy.acceptsMark]
  | childStar f =>
    rcases allowed with ⟨run,limit,valid,fits,shapeIs,childFits⟩
    change shape = .any at shapeIs
    subst shape
    cases mark <;>
      simp_all [templateActual,render,intrinsic,legalActual,emit,selected,table,
        commonLegal,Allowed,admissionLayer,joinLayer,one_child_relation,
        concrete,RestrictedInitialPolicy.acceptsMark]
  | childExact f =>
    rcases allowed with ⟨run,limit,valid,fits,shapeIs,full,childFits⟩
    change shape = .any at shapeIs
    subst shape
    cases mark with
    | flow => simp [concrete] at full
    | full n =>
      simp_all [templateActual,render,intrinsic,legalActual,emit,selected,table,
        commonLegal,Allowed,admissionLayer,joinLayer,one_child_relation,
        concrete,RestrictedInitialPolicy.acceptsMark]
  | rootStar =>
    rcases allowed with ⟨run,limit,valid,fits,cell⟩
    rcases cell with anyShape | ⟨starShape,runTwo,room⟩
    · change shape = .any at anyShape
      subst shape
      cases mark <;>
        simp_all [templateActual,render,starE,intrinsic,legalActual,emit,selected,table,
          commonLegal,Allowed,admissionLayer,joinLayer,same_path_relation,
          RestrictedInitialPolicy.acceptsMark]
    · change shape = .star at starShape
      subst shape
      change path.length < mode.limit at room
      have childFits : (path ++ [freshField (demandE ⟨base,path,.star,mark,e⟩)]).length
          ≤ mode.limit := by simp only [List.length_append,List.length_singleton]; omega
      have fresh := freshField_is_admitted (demandE ⟨base,path,.star,mark,e⟩)
      cases mark <;>
        simp_all [templateActual,render,starE,intrinsic,legalActual,emit,selected,table,
          commonLegal,Allowed,demandAdmits,admissionLayer,joinLayer,one_child_relation,
          RestrictedInitialPolicy.acceptsMark]

/- Relative templates depend only on the queried stored coordinate. There
is no finite universe of paths/marks and no enumeration of actual facts. -/
def relativeTemplates (d : Demand) (initial : Pattern) : List Template :=
  if initial.path = d.path then [.rootExact,.rootStar,.rootMust initial.exclusion]
  else match dropPrefix d.path initial.path with
    | some [f] => [.childStar f,.childExact f]
    | _ => []

def templateTest (mode : Mode) (d : Demand) (initial : Pattern) (t : Template) : Bool :=
  decide (Allowed mode d t ∧ render d t = initial)

def imageTemplate (mode : Mode) (d : Demand) (initial : Pattern) : Option Template :=
  (relativeTemplates d initial).find? (templateTest mode d initial)

def rawImage (mode : Mode) (d : Demand) (initial : Pattern) : Bool :=
  (imageTemplate mode d initial).isSome

theorem render_is_in_relative_templates (d : Demand) (t : Template) :
    t ∈ relativeTemplates d (render d t) := by
  cases t with
  | rootExact => simp [relativeTemplates,render]
  | rootStar => simp [relativeTemplates,render]
  | rootMust e => simp [relativeTemplates,render]
  | childStar f =>
    have different : d.path ++ [f] ≠ d.path := by
      intro same
      have lengths := congrArg List.length same
      simp only [List.length_append,List.length_singleton] at lengths
      omega
    have prefixPath : dropPrefix d.path (d.path ++ [f]) = some [f] :=
      CoreAux.dropPrefix_some.mpr rfl
    simp [relativeTemplates,render,different,prefixPath]
  | childExact f =>
    have different : d.path ++ [f] ≠ d.path := by
      intro same
      have lengths := congrArg List.length same
      simp only [List.length_append,List.length_singleton] at lengths
      omega
    have prefixPath : dropPrefix d.path (d.path ++ [f]) = some [f] :=
      CoreAux.dropPrefix_some.mpr rfl
    simp [relativeTemplates,render,different,prefixPath]

theorem raw_image_iff_relative_allowed_template (mode : Mode) (d : Demand) (initial : Pattern) :
    rawImage mode d initial = true ↔
      ∃ t, Allowed mode d t ∧ render d t = initial := by
  constructor
  · intro present
    obtain ⟨t,member,accepted⟩ := List.find?_isSome.mp present
    exact ⟨t,of_decide_eq_true accepted⟩
  · rintro ⟨t,allowed,same⟩
    apply List.find?_isSome.mpr
    refine ⟨t,?_,decide_eq_true ⟨allowed,same⟩⟩
    rw [← same]
    exact render_is_in_relative_templates d t

theorem arbitrary_actual_emission_is_in_raw_image
    (mode : Mode) (d : Demand) (a : Actual) (seed : Seed)
    (emitted : emit mode d a = some seed) : rawImage mode d seed.initial = true := by
  cases chosen : selected mode d a with
  | none => simp [emit,chosen] at emitted
  | some t =>
    have same : { initial := render d t, layer := admissionLayer (render d t) a } = seed := by
      simpa [emit,chosen] using emitted
    apply (raw_image_iff_relative_allowed_template mode d seed.initial).mpr
    exact ⟨t,selected_is_allowed mode d a t chosen,congrArg Seed.initial same⟩

def actualWitness (mode : Mode) (d : Demand) (initial : Pattern) : Option Actual :=
  (imageTemplate mode d initial).map (templateActual d)

theorem raw_image_supplies_actual_witness (mode : Mode) (d : Demand) (initial : Pattern)
    (present : rawImage mode d initial = true) :
    ∃ a, actualWitness mode d initial = some a ∧ legalActual mode a ∧
      emit mode d a = some ⟨initial,intrinsic initial⟩ := by
  cases chosen : imageTemplate mode d initial with
  | none => simp [rawImage,chosen] at present
  | some t =>
    have tested : templateTest mode d initial t = true := List.find?_some chosen
    obtain ⟨allowed,same⟩ := of_decide_eq_true tested
    obtain ⟨legal,emitted⟩ := allowed_template_has_legal_executable_witness mode d t allowed
    refine ⟨templateActual d t,by simp [actualWitness,chosen],legal,?_⟩
    simpa only [same] using emitted

theorem raw_image_exactly_characterizes_arbitrary_emission
    (mode : Mode) (d : Demand) (initial : Pattern) :
    rawImage mode d initial = true ↔
      ∃ a seed, emit mode d a = some seed ∧ seed.initial = initial := by
  constructor
  · intro present
    obtain ⟨a,found,legal,emitted⟩ := raw_image_supplies_actual_witness mode d initial present
    exact ⟨a,⟨initial,intrinsic initial⟩,emitted,rfl⟩
  · rintro ⟨a,seed,emitted,same⟩
    rw [← same]
    exact arbitrary_actual_emission_is_in_raw_image mode d a seed emitted

theorem raw_image_preserves_base_mark_budget_and_has_no_ANY
    (mode : Mode) (d : Demand) (initial : Pattern)
    (present : rawImage mode d initial = true) :
    initial.base = d.base ∧ initial.mark = d.mark ∧
    initial.path.length ≤ mode.limit ∧ initial.tail ≠ .any ∧
    (initial.path = d.path ∨ ∃ f, initial.path = d.path ++ [f]) := by
  obtain ⟨t,allowed,same⟩ :=
    (raw_image_iff_relative_allowed_template mode d initial).mp present
  rw [← same]
  rcases allowed with ⟨run,limit,valid,fits,cell⟩
  cases t with
  | rootExact => exact ⟨rfl,rfl,fits,by simp [render],Or.inl rfl⟩
  | rootStar => exact ⟨rfl,rfl,fits,by simp [render],Or.inl rfl⟩
  | rootMust e => exact ⟨rfl,rfl,fits,by simp [render],Or.inl rfl⟩
  | childStar f =>
    refine ⟨rfl,rfl,?_,by simp [render],Or.inr ⟨f,rfl⟩⟩
    simpa only [render,List.length_append,List.length_singleton] using cell.2
  | childExact f =>
    refine ⟨rfl,rfl,?_,by simp [render],Or.inr ⟨f,rfl⟩⟩
    simpa only [render,List.length_append,List.length_singleton] using cell.2.2

/- The joint image does not discard supplied concrete support. FLOW has its
intrinsic layer; a concrete intrinsically-DEMAND initial cannot be NORMAL;
other concrete initials may be NORMAL or DEMAND. -/
def JointLayer (initial : Pattern) (layer : Layer) : Prop :=
  match initial.mark with
  | .flow => layer = intrinsic initial
  | .full _ => intrinsic initial = .normal ∨ layer = .demand

instance (initial : Pattern) (layer : Layer) : Decidable (JointLayer initial layer) := by
  unfold JointLayer
  cases initial.mark <;> infer_instance

theorem join_demand_left (layer : Layer) : joinLayer .demand layer = .demand := by
  cases layer <;> rfl

theorem join_demand_right (layer : Layer) : joinLayer layer .demand = .demand := by
  cases layer <;> rfl

theorem legal_actual_may_be_relayered_DEMAND (mode : Mode) (a : Actual)
    (legal : legalActual mode a) : legalActual mode {a with layer := .demand} := by
  rcases a with ⟨⟨base,path,tail,mark,e⟩,layer,h⟩
  cases tail <;> cases mark <;> simp_all [legalActual]

theorem selected_implies_common_legal (mode : Mode) (d : Demand) (a : Actual) (t : Template)
    (found : selected mode d a = some t) : commonLegal mode d a := by
  by_cases common : commonLegal mode d a
  · exact common
  · simp [selected,table,common] at found

theorem concrete_emission_keeps_DEMAND_relayering
    (mode : Mode) (d : Demand) (a : Actual) (seed : Seed) (mark : Nat)
    (emitted : emit mode d a = some seed) (full : seed.initial.mark = .full mark) :
    legalActual mode {a with layer := .demand} ∧
      emit mode d {a with layer := .demand} = some ⟨seed.initial,.demand⟩ := by
  cases chosen : selected mode d a with
  | none => simp [emit,chosen] at emitted
  | some t =>
    have same : { initial := render d t, layer := admissionLayer (render d t) a } = seed := by
      simpa [emit,chosen] using emitted
    have common := selected_implies_common_legal mode d a t chosen
    rcases common with ⟨run,limit,valid,fits,legal,baseMatches,markMatches,provisional⟩
    have legalNew := legal_actual_may_be_relayered_DEMAND mode a legal
    have commonOld : commonLegal mode d a :=
      ⟨run,limit,valid,fits,legal,baseMatches,markMatches,provisional⟩
    have commonNew : commonLegal mode d {a with layer := .demand} :=
      ⟨run,limit,valid,fits,legalNew,baseMatches,markMatches,provisional⟩
    have sameTable : table mode d {a with layer := .demand} = table mode d a := by
      simp only [table,if_pos commonOld,if_pos commonNew]
    have sameSelected : selected mode d {a with layer := .demand} = some t := by
      simpa only [selected,sameTable] using chosen
    have sameInitial : render d t = seed.initial := congrArg Seed.initial same
    have renderedFull : (render d t).mark = .full mark := by
      rw [sameInitial]
      exact full
    have layerNew : admissionLayer (render d t) {a with layer := .demand} = .demand := by
      simp only [admissionLayer,renderedFull,join_demand_left,join_demand_right]
    refine ⟨legalNew,?_⟩
    unfold emit
    rw [sameSelected]
    change some (⟨render d t,admissionLayer (render d t) {a with layer := .demand}⟩ : Seed) =
      some (⟨seed.initial,.demand⟩ : Seed)
    rw [layerNew,sameInitial]

theorem admission_layer_satisfies_joint_layer (initial : Pattern) (a : Actual) :
    JointLayer initial (admissionLayer initial a) := by
  cases initial with
  | mk base path tail mark e =>
    cases mark with
    | flow => rfl
    | full n =>
      cases tail <;>
        simp [JointLayer,admissionLayer,intrinsic,join_demand_left]

theorem joint_layer_has_constructive_alternative (initial : Pattern) (layer : Layer)
    (joint : JointLayer initial layer) :
    layer = intrinsic initial ∨ ∃ mark, initial.mark = .full mark ∧ layer = .demand := by
  cases markIs : initial.mark with
  | flow =>
    simp only [JointLayer,markIs] at joint
    exact Or.inl joint
  | full n =>
    simp only [JointLayer,markIs] at joint
    rcases joint with normal | demand
    · cases layer with
      | normal => exact Or.inl normal.symm
      | demand => exact Or.inr ⟨n,rfl,rfl⟩
    · exact Or.inr ⟨n,rfl,demand⟩

def jointImage (mode : Mode) (d : Demand) (seed : Seed) : Bool :=
  rawImage mode d seed.initial && decide (JointLayer seed.initial seed.layer)

def jointActualWitness (mode : Mode) (d : Demand) (seed : Seed) : Option Actual := do
  let a ← actualWitness mode d seed.initial
  if seed.layer = intrinsic seed.initial then pure a
  else pure {a with layer := .demand}

theorem joint_image_has_executable_actual_witness (mode : Mode) (d : Demand) (seed : Seed)
    (present : jointImage mode d seed = true) :
    ∃ actual, jointActualWitness mode d seed = some actual ∧ legalActual mode actual ∧
      emit mode d actual = some seed := by
  obtain ⟨image,joint⟩ := Bool.and_eq_true_iff.mp present
  have joint' : JointLayer seed.initial seed.layer := of_decide_eq_true joint
  obtain ⟨actual,found,legal,emitted⟩ := raw_image_supplies_actual_witness mode d seed.initial image
  by_cases sameLayer : seed.layer = intrinsic seed.initial
  · refine ⟨actual,by simp [jointActualWitness,found,sameLayer],legal,?_⟩
    cases seed with
    | mk initial layer =>
      change layer = intrinsic initial at sameLayer
      change emit mode d actual = some (⟨initial,layer⟩ : Seed)
      rw [sameLayer]
      exact emitted
  · rcases joint_layer_has_constructive_alternative seed.initial seed.layer joint' with same | ⟨n,full,demand⟩
    · exact False.elim (sameLayer same)
    · obtain ⟨legalNew,emittedNew⟩ := concrete_emission_keeps_DEMAND_relayering
        mode d actual ⟨seed.initial,intrinsic seed.initial⟩ n emitted full
      refine ⟨{actual with layer := .demand},by simp [jointActualWitness,found,sameLayer],legalNew,?_⟩
      cases seed with
      | mk initial layer =>
        change layer = .demand at demand
        change emit mode d {actual with layer := .demand} = some (⟨initial,layer⟩ : Seed)
        rw [demand]
        exact emittedNew

theorem joint_image_exactly_characterizes_arbitrary_admission
    (mode : Mode) (d : Demand) (seed : Seed) :
    jointImage mode d seed = true ↔ ∃ actual, emit mode d actual = some seed := by
  constructor
  · intro present
    obtain ⟨actual,found,legal,emitted⟩ := joint_image_has_executable_actual_witness mode d seed present
    exact ⟨actual,emitted⟩
  · rintro ⟨actual,emitted⟩
    have image := arbitrary_actual_emission_is_in_raw_image mode d actual seed emitted
    cases chosen : selected mode d actual with
    | none => simp [emit,chosen] at emitted
    | some t =>
      have same : { initial := render d t, layer := admissionLayer (render d t) actual } = seed := by
        simpa [emit,chosen] using emitted
      have joint := admission_layer_satisfies_joint_layer (render d t) actual
      rw [← same]
      exact Bool.and_eq_true_iff.mpr ⟨by simpa only [← same] using image,decide_eq_true joint⟩

/- Ordinary location containment of a raw initial. At the same STAR head,
the initial's exclusions must include the demand's exclusions. C5 applies
this to the raw preimage, not to a wider normalized public FLOW STAR key. -/
def insideDemand (d : Demand) (initial : Pattern) : Bool :=
  decide (initial.base = d.base) &&
    RestrictedInitialPolicy.acceptsMark d.mark initial.mark &&
    match dropPrefix d.path initial.path with
    | none => false
    | some rest =>
      match d.shape with
      | .any => true
      | .exact => rest.isEmpty && decide (initial.tail = .exact)
      | .star =>
        if rest.isEmpty then
          decide (initial.tail = .exact) ||
            (demandE d).all (fun f => memB f initial.exclusion)
        else demandAdmits d rest

theorem exclusions_include_themselves (e : List Nat) :
    e.all (fun f => memB f e) = true := by
  exact List.all_eq_true.mpr (fun f member => CoreAux.memB_iff.mpr member)

theorem every_raw_image_is_inside_its_demand (mode : Mode) (d : Demand) (initial : Pattern)
    (present : rawImage mode d initial = true) : insideDemand d initial = true := by
  obtain ⟨t,allowed,same⟩ :=
    (raw_image_iff_relative_allowed_template mode d initial).mp present
  rw [← same]
  have self : dropPrefix d.path d.path = some [] :=
    ApSpec.Handoff.RAux.dropPrefix_self' d.path
  cases t with
  | rootExact =>
    cases d with
    | mk base path shape mark e =>
      cases shape <;> cases mark <;>
        simp [insideDemand,render,self,RestrictedInitialPolicy.acceptsMark]
  | rootStar =>
    rcases allowed with ⟨run,limit,valid,fits,cell⟩
    rcases cell with anyShape | ⟨starShape,runTwo,room⟩
    · cases d with
      | mk base path shape mark e =>
        change shape = .any at anyShape
        subst shape
        cases mark <;> simp [insideDemand,render,self,RestrictedInitialPolicy.acceptsMark]
    · cases d with
      | mk base path shape mark e =>
        change shape = .star at starShape
        subst shape
        cases mark <;>
          simp [insideDemand,render,starE,self,exclusions_include_themselves,
            RestrictedInitialPolicy.acceptsMark]
  | rootMust e =>
    rcases allowed with ⟨run,limit,valid,fits,anyShape,directionIs⟩
    cases d with
    | mk base path shape mark excluded =>
      change shape = .any at anyShape
      subst shape
      cases mark <;> simp [insideDemand,render,self,RestrictedInitialPolicy.acceptsMark]
  | childStar f =>
    rcases allowed with ⟨run,limit,valid,fits,anyShape,childFits⟩
    have child : dropPrefix d.path (d.path ++ [f]) = some [f] :=
      CoreAux.dropPrefix_some.mpr rfl
    cases d with
    | mk base path shape mark e =>
      change shape = .any at anyShape
      subst shape
      cases mark <;> simp [insideDemand,render,child,RestrictedInitialPolicy.acceptsMark]
  | childExact f =>
    rcases allowed with ⟨run,limit,valid,fits,anyShape,full,childFits⟩
    have child : dropPrefix d.path (d.path ++ [f]) = some [f] :=
      CoreAux.dropPrefix_some.mpr rfl
    cases d with
    | mk base path shape mark e =>
      change shape = .any at anyShape
      subst shape
      cases mark <;> simp [insideDemand,render,child,RestrictedInitialPolicy.acceptsMark]

/- This entry normalizer models a public conditional FLOW pair. The complete
native pair must normalize both endpoints; ND/Target adapters are separate.
An emitted EXACT initial has Empty E, so its public STAR inverse is exact. -/
def publicInitial (raw : Pattern) : Pattern :=
  match raw.tail, raw.mark with
  | .exact, .flow => { raw with tail := .star }
  | _, _ => raw

def rawPreimages (stored : Pattern) : List Pattern :=
  match stored.tail, stored.mark with
  | .star, .flow => [stored,{stored with tail := .exact}]
  | _, _ => [stored]

theorem raw_is_in_public_preimages (raw : Pattern) :
    raw ∈ rawPreimages (publicInitial raw) := by
  cases raw with
  | mk base path tail mark e =>
    cases tail <;> cases mark <;> simp [rawPreimages,publicInitial]

theorem listed_preimages_normalize_to_public (stored raw : Pattern)
    (member : raw ∈ rawPreimages stored)
    (canonical : publicInitial stored = stored) : publicInitial raw = stored := by
  cases stored with
  | mk base path tail mark e =>
    cases tail <;> cases mark <;> simp [rawPreimages] at member
    all_goals first
      | (subst raw; exact canonical)
      | (rcases member with same | same <;> cases same <;>
          simp_all [publicInitial])

def storedTest (mode : Mode) (d : Demand) (stored raw : Pattern) : Bool :=
  rawImage mode d raw && (insideDemand d raw && decide (publicInitial raw = stored))

def storePreimage (mode : Mode) (d : Demand) (stored : Pattern) : Option Pattern :=
  (rawPreimages stored).find? (storedTest mode d stored)

def canStoreInitial (mode : Mode) (d : Demand) (stored : Pattern) : Bool :=
  (storePreimage mode d stored).isSome

structure StoredWitness where
  rawInitial : Pattern
  actual : Actual
deriving DecidableEq, Repr

def storedWitness (mode : Mode) (d : Demand) (stored : Pattern) : Option StoredWitness := do
  let raw ← storePreimage mode d stored
  let actual ← actualWitness mode d raw
  pure ⟨raw,actual⟩

theorem C5_permission_has_executable_raw_actual_witness
    (mode : Mode) (d : Demand) (stored : Pattern)
    (permitted : canStoreInitial mode d stored = true) :
    ∃ witness, storedWitness mode d stored = some witness ∧
      legalActual mode witness.actual ∧
      emit mode d witness.actual =
        some ⟨witness.rawInitial,intrinsic witness.rawInitial⟩ ∧
      publicInitial witness.rawInitial = stored ∧ insideDemand d witness.rawInitial = true := by
  cases found : storePreimage mode d stored with
  | none => simp [canStoreInitial,found] at permitted
  | some raw =>
    have accepted : storedTest mode d stored raw = true := List.find?_some found
    obtain ⟨image,inside,normal⟩ := by
      simpa only [storedTest,Bool.and_eq_true,decide_eq_true_eq] using accepted
    obtain ⟨actual,chosen,legal,emitted⟩ := raw_image_supplies_actual_witness mode d raw image
    refine ⟨⟨raw,actual⟩,?_,legal,emitted,normal,inside⟩
    simp [storedWitness,found,chosen]

theorem C5_permission_iff_normalized_actual_emission
    (mode : Mode) (d : Demand) (stored : Pattern) :
    canStoreInitial mode d stored = true ↔
      ∃ actual seed, emit mode d actual = some seed ∧
        publicInitial seed.initial = stored ∧ insideDemand d seed.initial = true := by
  constructor
  · intro permitted
    obtain ⟨witness,found,legal,emitted,normal,inside⟩ :=
      C5_permission_has_executable_raw_actual_witness mode d stored permitted
    exact ⟨witness.actual,⟨witness.rawInitial,intrinsic witness.rawInitial⟩,
      emitted,normal,inside⟩
  · rintro ⟨actual,seed,emitted,normal,inside⟩
    have image := arbitrary_actual_emission_is_in_raw_image mode d actual seed emitted
    apply List.find?_isSome.mpr
    refine ⟨seed.initial,?_,?_⟩
    · rw [← normal]
      exact raw_is_in_public_preimages seed.initial
    · simp [storedTest,image,inside,normal]

/- C5 entry permission does not couple the stored conclusion layer to the
seed layer. A typed output plus its literal protection is transported. -/
structure Output where
  pattern : Pattern
  layer : Layer
  hasProtection : Bool
deriving DecidableEq, Repr

def acceptOutput (mode : Mode) (d : Demand) (stored : Pattern) (output : Output) : Option Output :=
  if canStoreInitial mode d stored then some output else none

theorem C5_entry_permission_preserves_supplied_output_and_H
    (mode : Mode) (d : Demand) (stored : Pattern) (output : Output)
    (permitted : canStoreInitial mode d stored = true) :
    acceptOutput mode d stored output = some output := by
  simp [acceptOutput,permitted]

theorem concrete_STAR_start_is_identity_DEMAND (base : Nat) (path e : List Nat) (mark : Nat)
    (supplied : Layer) :
    start ⟨⟨base,path,.star,.full mark,e⟩,supplied⟩ =
      ⟨⟨base,path,.star,.full mark,e⟩,.demand,false⟩ := by
  cases supplied <;> rfl

theorem FLOW_STAR_start_is_identity_NORMAL (base : Nat) (path e : List Nat) :
    start ⟨⟨base,path,.star,.flow,e⟩,.normal⟩ =
      ⟨⟨base,path,.star,.flow,e⟩,.normal,false⟩ := rfl

theorem concrete_STAR_actual_requires_DEMAND (mode : Mode) (base : Nat) (path e : List Nat)
    (mark : Nat) (layer : Layer) (h : Bool)
    (legal : legalActual mode ⟨⟨base,path,.star,.full mark,e⟩,layer,h⟩) :
    layer = .demand := legal.2

theorem FLOW_admission_uses_intrinsic_only (initial : Pattern) (a : Actual)
    (flow : initial.mark = .flow) :
    admissionLayer initial a = intrinsic initial := by simp [admissionLayer,flow]

theorem EXACT_on_MAY_concrete_support_is_kept (base : Nat) (path : List Nat) (mark : Nat)
    (actualBase : Nat) (actualPath : List Nat) (actualMark : ScalarMark)
    (actualLayer : Layer) (h : Bool) :
    admissionLayer ⟨base,path,.exact,.full mark,[]⟩
      ⟨⟨actualBase,actualPath,.any,actualMark,[]⟩,actualLayer,h⟩ = .demand := by
  cases actualLayer <;> rfl

theorem STAR_identity_uses_correlated_continuations (e sigma tau : List Nat) :
    tailF (.star (.set e)) sigma tau ↔ tau = sigma ∧ (Excl.set e).admits sigma = true := Iff.rfl

theorem STAR_identity_cannot_invent_an_independent_continuation (e : List Nat) (x y : Nat)
    (derived : tailF (.star (.set e)) [x] [y]) : y = x := by
  exact (List.cons.inj derived.1).1

theorem mark_mismatch_never_emits (mode : Mode) (d : Demand) (a : Actual)
    (mismatch : RestrictedInitialPolicy.acceptsMark d.mark a.pattern.mark = false) :
    emit mode d a = none := by
  simp [emit,selected,table,commonLegal,mismatch]

theorem base_mismatch_never_emits (mode : Mode) (d : Demand) (a : Actual)
    (mismatch : d.base ≠ a.pattern.base) : emit mode d a = none := by
  simp [emit,selected,table,commonLegal,mismatch]

theorem illegal_actual_never_emits (mode : Mode) (d : Demand) (a : Actual)
    (illegal : ¬ legalActual mode a) : emit mode d a = none := by
  simp [emit,selected,table,commonLegal,illegal]

theorem later_STAR_demand_rejects_every_strict_descendant
    (mode : Mode) (d : Demand) (a : Actual) (field : Nat) (rest : List Nat)
    (star : d.shape = .star) (later : mode.run ≠ 2)
    (below : relate d.path a.pattern.path = .below (field :: rest)) :
    emit mode d a = none := by
  by_cases common : commonLegal mode d a
  · simp [emit,selected,table,common,star,below,later]
  · simp [emit,selected,table,common]

theorem ordinary_STAR_ancestor_does_not_gain_MAY_capability
    (mode : Mode) (d : Demand) (a : Actual) (rest : List Nat)
    (anyDemand : d.shape = .any) (starActual : a.pattern.tail = .star)
    (above : relate d.path a.pattern.path = .above rest) : emit mode d a = none := by
  by_cases common : commonLegal mode d a
  · simp [emit,selected,table,common,anyDemand,starActual,above]
  · simp [emit,selected,table,common]

def keepHandoff (d : Demand) : Demand := d

theorem handoff_does_not_refine_precise_STAR (d : Demand) : keepHandoff d = d := rfl

def mode3 : Mode := ⟨3,3,.forward⟩
def staticLikePrecise : Demand := ⟨31,[7],.star,.full 1,[]⟩
def deeperNormal : Actual := ⟨⟨31,[7,8],.exact,.full 1,[]⟩,.normal,false⟩

theorem precise_STAR_deeper_actual_still_rejects :
    emit mode3 staticLikePrecise deeperNormal = none := by decide

theorem same_head_ANY_accepts_legal_concrete_STAR_as_identity_DEMAND :
    emit mode3 ⟨31,[7],.any,.full 1,[]⟩
      ⟨⟨31,[7],.star,.full 1,[8]⟩,.demand,true⟩ =
      some ⟨⟨31,[7],.star,.full 1,[]⟩,.demand⟩ := by decide

theorem concrete_demand_never_admits_companion_FLOW :
    emit mode3 ⟨31,[7],.any,.full 1,[]⟩
      ⟨⟨31,[7],.star,.flow,[]⟩,.normal,false⟩ = none := by decide

theorem FLOW_EXACT_preimage_is_needed_at_later_STAR_cap :
    rawImage ⟨3,1,.forward⟩ ⟨31,[7],.star,.flow,[]⟩
      ⟨31,[7],.star,.flow,[]⟩ = false ∧
    canStoreInitial ⟨3,1,.forward⟩ ⟨31,[7],.star,.flow,[]⟩
      ⟨31,[7],.star,.flow,[]⟩ = true := by decide

theorem seed_and_output_layers_are_not_equal_by_contract :
    ∃ output : Output,
      output.layer = .demand ∧
      acceptOutput ⟨3,1,.forward⟩ ⟨31,[7],.star,.flow,[]⟩
        ⟨31,[7],.star,.flow,[]⟩ output = some output := by
  exact ⟨⟨⟨40,[],.any,.full 1,[]⟩,.demand,true⟩,rfl,by decide⟩

/- Executable native-shaped table cells. They are regression examples, not
a finite universe used by the general image proofs above. -/
def executableCells : List Bool := [
  decide (emit mode3 ⟨3,[],.any,.flow,[]⟩
    ⟨⟨3,[],.any,.full 137,[]⟩,.demand,false⟩ =
      some ⟨⟨3,[],.star,.flow,[]⟩,.normal⟩),
  decide (emit mode3 ⟨3,[],.any,.full 137,[]⟩
    ⟨⟨3,[],.any,.full 137,[]⟩,.demand,false⟩ =
      some ⟨⟨3,[],.star,.full 137,[]⟩,.demand⟩),
  decide (emit mode3 ⟨3,[],.exact,.full 137,[]⟩
    ⟨⟨3,[],.any,.full 137,[]⟩,.demand,false⟩ =
      some ⟨⟨3,[],.exact,.full 137,[]⟩,.demand⟩),
  decide (emit mode3 ⟨3,[],.exact,.flow,[]⟩
    ⟨⟨3,[],.any,.full 137,[]⟩,.demand,false⟩ = none),
  decide (emit mode3 ⟨3,[],.any,.flow,[]⟩
    ⟨⟨3,[41],.exact,.full 137,[]⟩,.normal,false⟩ =
      some ⟨⟨3,[41],.star,.flow,[]⟩,.normal⟩),
  decide (emit mode3 ⟨3,[],.any,.full 137,[]⟩
    ⟨⟨3,[41],.exact,.full 137,[]⟩,.normal,false⟩ =
      some ⟨⟨3,[41],.exact,.full 137,[]⟩,.normal⟩),
  decide (emit mode3 ⟨3,[],.any,.full 137,[]⟩
    ⟨⟨3,[41,42],.exact,.full 137,[]⟩,.normal,false⟩ =
      some ⟨⟨3,[41],.star,.full 137,[]⟩,.demand⟩),
  decide (emit mode3 ⟨3,[41],.any,.full 137,[]⟩
    ⟨⟨3,[],.any,.full 137,[]⟩,.demand,false⟩ =
      some ⟨⟨3,[41],.star,.full 137,[]⟩,.demand⟩),
  decide (emit mode3 ⟨3,[41],.any,.full 137,[]⟩
    ⟨⟨3,[],.star,.full 137,[]⟩,.demand,false⟩ = none),
  decide (emit mode3 ⟨3,[41],.any,.full 137,[]⟩
    ⟨⟨3,[],.must,.full 137,[]⟩,.normal,false⟩ =
      some ⟨⟨3,[41],.must,.full 137,[]⟩,.normal⟩),
  decide (emit mode3 ⟨3,[41],.any,.full 137,[]⟩
    ⟨⟨3,[],.must,.full 137,[41]⟩,.normal,false⟩ = none),
  decide (emit mode3 ⟨3,[],.any,.full 137,[]⟩
    ⟨⟨3,[],.must,.full 137,[41]⟩,.normal,false⟩ =
      some ⟨⟨3,[],.must,.full 137,[41]⟩,.normal⟩),
  decide (emit ⟨2,3,.backward⟩ ⟨3,[],.any,.full 137,[]⟩
    ⟨⟨3,[],.must,.full 137,[41]⟩,.normal,false⟩ = none),
  decide (emit ⟨2,3,.backward⟩ ⟨3,[],.star,.full 137,[42]⟩
    ⟨⟨3,[41],.exact,.full 137,[]⟩,.normal,false⟩ =
      some ⟨⟨3,[],.star,.full 137,[42]⟩,.demand⟩),
  decide (emit ⟨2,3,.backward⟩ ⟨3,[],.star,.full 137,[41]⟩
    ⟨⟨3,[41],.exact,.full 137,[]⟩,.normal,false⟩ = none),
  decide (emit ⟨2,3,.backward⟩ ⟨3,[],.star,.flow,[41]⟩
    ⟨⟨3,[41],.exact,.full 137,[]⟩,.normal,false⟩ =
      some ⟨⟨3,[],.star,.flow,[]⟩,.normal⟩),
  decide (emit mode3 ⟨3,[],.any,.full 137,[]⟩
    ⟨⟨3,[],.star,.full 137,[]⟩,.normal,false⟩ = none),
  decide (emit mode3 ⟨3,[],.any,.full 137,[]⟩
    ⟨⟨3,[],.exact,.full 138,[]⟩,.normal,false⟩ = none),
  decide (emit mode3 ⟨3,[],.any,.full 137,[]⟩
    ⟨⟨4,[],.exact,.full 137,[]⟩,.normal,false⟩ = none),
  decide (rawImage ⟨2,1,.backward⟩ ⟨3,[41],.star,.full 137,[]⟩
    ⟨3,[41],.star,.full 137,[]⟩ = false),
  decide (rawImage ⟨2,2,.backward⟩ ⟨3,[41],.star,.full 137,[0,1,2,3]⟩
    ⟨3,[41],.star,.full 137,[0,1,2,3]⟩ = true),
  decide (canStoreInitial ⟨3,1,.forward⟩ ⟨3,[41],.exact,.flow,[]⟩
    ⟨3,[41],.star,.flow,[]⟩ = true),
  decide (rawImage mode3 ⟨3,[],.any,.full 137,[]⟩
    ⟨3,[],.any,.full 137,[]⟩ = false),
  decide (jointImage mode3 ⟨3,[],.any,.full 137,[]⟩
    ⟨⟨3,[],.star,.full 137,[]⟩,.normal⟩ = false)
]

#eval "PLAIN_STAR_RELATIVE_CELLS=" ++ toString (executableCells.all id)

end PlainStarRelativeAdmission

#print axioms PlainStarRelativeAdmission.member_bounded_by_maxField
#print axioms PlainStarRelativeAdmission.freshField_not_member
#print axioms PlainStarRelativeAdmission.freshField_is_admitted
#print axioms PlainStarRelativeAdmission.selected_is_allowed
#print axioms PlainStarRelativeAdmission.same_path_relation
#print axioms PlainStarRelativeAdmission.one_child_relation
#print axioms PlainStarRelativeAdmission.allowed_template_has_legal_executable_witness
#print axioms PlainStarRelativeAdmission.render_is_in_relative_templates
#print axioms PlainStarRelativeAdmission.raw_image_iff_relative_allowed_template
#print axioms PlainStarRelativeAdmission.arbitrary_actual_emission_is_in_raw_image
#print axioms PlainStarRelativeAdmission.raw_image_supplies_actual_witness
#print axioms PlainStarRelativeAdmission.raw_image_exactly_characterizes_arbitrary_emission
#print axioms PlainStarRelativeAdmission.raw_image_preserves_base_mark_budget_and_has_no_ANY
#print axioms PlainStarRelativeAdmission.join_demand_left
#print axioms PlainStarRelativeAdmission.join_demand_right
#print axioms PlainStarRelativeAdmission.legal_actual_may_be_relayered_DEMAND
#print axioms PlainStarRelativeAdmission.selected_implies_common_legal
#print axioms PlainStarRelativeAdmission.concrete_emission_keeps_DEMAND_relayering
#print axioms PlainStarRelativeAdmission.admission_layer_satisfies_joint_layer
#print axioms PlainStarRelativeAdmission.joint_layer_has_constructive_alternative
#print axioms PlainStarRelativeAdmission.joint_image_has_executable_actual_witness
#print axioms PlainStarRelativeAdmission.joint_image_exactly_characterizes_arbitrary_admission
#print axioms PlainStarRelativeAdmission.exclusions_include_themselves
#print axioms PlainStarRelativeAdmission.every_raw_image_is_inside_its_demand
#print axioms PlainStarRelativeAdmission.raw_is_in_public_preimages
#print axioms PlainStarRelativeAdmission.listed_preimages_normalize_to_public
#print axioms PlainStarRelativeAdmission.C5_permission_has_executable_raw_actual_witness
#print axioms PlainStarRelativeAdmission.C5_permission_iff_normalized_actual_emission
#print axioms PlainStarRelativeAdmission.C5_entry_permission_preserves_supplied_output_and_H
#print axioms PlainStarRelativeAdmission.concrete_STAR_start_is_identity_DEMAND
#print axioms PlainStarRelativeAdmission.FLOW_STAR_start_is_identity_NORMAL
#print axioms PlainStarRelativeAdmission.concrete_STAR_actual_requires_DEMAND
#print axioms PlainStarRelativeAdmission.FLOW_admission_uses_intrinsic_only
#print axioms PlainStarRelativeAdmission.EXACT_on_MAY_concrete_support_is_kept
#print axioms PlainStarRelativeAdmission.STAR_identity_uses_correlated_continuations
#print axioms PlainStarRelativeAdmission.STAR_identity_cannot_invent_an_independent_continuation
#print axioms PlainStarRelativeAdmission.mark_mismatch_never_emits
#print axioms PlainStarRelativeAdmission.base_mismatch_never_emits
#print axioms PlainStarRelativeAdmission.illegal_actual_never_emits
#print axioms PlainStarRelativeAdmission.later_STAR_demand_rejects_every_strict_descendant
#print axioms PlainStarRelativeAdmission.ordinary_STAR_ancestor_does_not_gain_MAY_capability
#print axioms PlainStarRelativeAdmission.handoff_does_not_refine_precise_STAR
#print axioms PlainStarRelativeAdmission.precise_STAR_deeper_actual_still_rejects
#print axioms PlainStarRelativeAdmission.same_head_ANY_accepts_legal_concrete_STAR_as_identity_DEMAND
#print axioms PlainStarRelativeAdmission.concrete_demand_never_admits_companion_FLOW
#print axioms PlainStarRelativeAdmission.FLOW_EXACT_preimage_is_needed_at_later_STAR_cap
#print axioms PlainStarRelativeAdmission.seed_and_output_layers_are_not_equal_by_contract
