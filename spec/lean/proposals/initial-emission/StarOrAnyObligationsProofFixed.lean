/-
Local supplement to the checked STAR_OR_ANY model. No native adapter or global
progress claim. ND is conjunction of predicates on the STAR-geometric projection.
Certificate inputs are Empty-E MAY cuts at any earlier counted-field prefix.
Point storage has opaque DATA work and an exact separate SOA Fact frontier;
pattern (including E/mark), layer and literal protection are all in its key.
-/
import StarOrAnyDesignProofFixed

namespace StarOrAnyObligations
open ApSpec StarOrAnyDesign
abbrev Mark := StarOrAnyDesign.Mark
abbrev Pattern := StarOrAnyDesign.Pattern
abbrev Fact := StarOrAnyDesign.Fact
abbrev Seed := StarOrAnyDesign.Seed
abbrev Mode := StarOrAnyDesign.Mode
abbrev Layer := StarOrAnyDesign.Layer
abbrev Input := StarOrAnyDesign.Input
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Executable exact duplicate removal. It does not use prefix coverage. -/
def literalDedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | first :: rest => if first ∈ rest then literalDedup rest else first :: literalDedup rest

theorem exact_dedup_preserves_membership {α : Type} [DecidableEq α]
    (value : α) (values : List α) : value ∈ literalDedup values ↔ value ∈ values := by
  induction values with
  | nil => simp [literalDedup]
  | cons first rest ih =>
    by_cases repeated : first ∈ rest
    · simp only [literalDedup,if_pos repeated,ih,List.mem_cons]
      constructor
      · intro member; exact Or.inr member
      · intro member
        cases member with
        | inl same => cases same; exact repeated
        | inr member => exact member
    · simp only [literalDedup,if_neg repeated,List.mem_cons,ih]

/-- Predicates may inspect all STAR geometry, mark and E. They may not inspect
C2's live marker. This is the stated public ND interpretation. -/
def geometric {W : Type} (predicate : Input → List Acc → W → Prop)
    (p : Pattern) (w : W) : Prop := predicate (scalar p) p.exclusion w
def conjunction {W : Type} (predicate : Input → List Acc → W → Prop)
    (members : List Pattern) (w : W) : Prop :=
  ∀ p, p ∈ members → geometric predicate p w
def normalizeND (members : List Pattern) : List Pattern := literalDedup (members.map erase)

theorem normalized_ND_member_dedup_keeps_the_geometric_conjunction
    {W : Type} (predicate : Input → List Acc → W → Prop)
    (members : List Pattern) (w : W) :
    conjunction predicate (normalizeND members) w ↔ conjunction predicate members w := by
  have erased : ∀ p : Pattern, geometric predicate (erase p) w ↔ geometric predicate p w := by
    intro p
    unfold geometric
    rw [(marker_erasure_keeps_only_the_STAR_geometric_projection p).1,
      (marker_erasure_keeps_only_the_STAR_geometric_projection p).2]
  constructor
  · intro normalized p member
    apply (erased p).mp
    apply normalized (erase p)
    apply (exact_dedup_preserves_membership (erase p) (members.map erase)).mpr
    exact List.mem_map.mpr ⟨p,member,rfl⟩
  · intro original p member
    have mapped := (exact_dedup_preserves_membership p (members.map erase)).mp member
    obtain ⟨raw,inOriginal,same⟩ := List.mem_map.mp mapped
    subst p
    exact (erased raw).mpr (original raw inOriginal)

/-- The prior scalar prefix lemma supplies the real old emission witness. The
new answer converts its MAY result to SOA and recalculates the current layer. -/
theorem earlier_MAY_prefix_cut_emits_the_same_SOA_joint_seed
    (run : Nat) (m : Mode) (b : Nat) (prefixPath suffix : List Acc)
    (required supplied : Mark)
    (restricted : 2 ≤ run)
    (markMatches : RestrictedInitialPolicy.acceptsMark required supplied = true)
    (budget : (prefixPath ++ suffix).length ≤ m.fieldLimit) :
    c2 .starThenMayForAny run m ⟨b,prefixPath ++ suffix,.any,required⟩
      ⟨fromInput (SelectedFullAdmission.mayAt b prefixPath supplied),.demand,false⟩ =
      [⟨⟨b,prefixPath ++ suffix,.starOrAny,required,[]⟩,intrinsicMark required⟩] := by
  let d : RestrictedInitialPolicy.Demand := ⟨b,prefixPath ++ suffix,.any,required⟩
  let actual : Input := SelectedFullAdmission.mayAt b prefixPath supplied
  let initial : Input := SelectedFullAdmission.mayAt b (prefixPath ++ suffix) required
  have prefixFits : prefixPath.length ≤ m.fieldLimit := by
    simp only [List.length_append] at budget
    omega
  have current : MayInitialToStarAudit.currentEmit m ⟨b,prefixPath ++ suffix,required⟩ actual = some initial :=
    SelectedFullAdmission.current_MAY_prefixes_emit_the_same_witness m b prefixPath suffix required supplied markMatches budget
  have boundedEmission : RestrictedInitialPolicy.DemandStarPolicy.emitAtBudget m.fieldLimit d actual = some initial := by
    change (match RestrictedInitialPolicy.DemandStarPolicy.emitAtBudget m.fieldLimit d actual with
      | none => none
      | some emitted => if MayInitialToStarAudit.directionLegal m.direction emitted then some emitted else none) = some initial at current
    cases observed : RestrictedInitialPolicy.DemandStarPolicy.emitAtBudget m.fieldLimit d actual with
    | none =>
      simp only [observed] at current
      cases current
    | some candidate =>
      simp only [observed] at current
      cases legal : MayInitialToStarAudit.directionLegal m.direction candidate with
      | false =>
        simp only [legal,Bool.false_eq_true,if_false] at current
        cases current
      | true =>
        have same : candidate = initial := by
          simpa only [legal,if_true,Option.some.injEq] using current
        exact congrArg some same
  have selectedRaw : RestrictedInitialPolicy.DemandStarPolicy.emit d actual = some initial :=
    (RestrictedInitialPolicy.DemandStarPolicy.budget_emission_facts m.fieldLimit d actual initial boundedEmission).2.2.1
  have noOverride : RestrictedInitialPolicy.DemandStarPolicy.overrideStar d actual = false := by
    simp [RestrictedInitialPolicy.DemandStarPolicy.overrideStar,d,RestrictedInitialPolicy.shapeEq]
  have ordinaryRaw : RestrictedInitialPolicy.emit d actual = some initial := by
    simpa only [RestrictedInitialPolicy.DemandStarPolicy.emit,noOverride,Bool.false_eq_true,if_false] using selectedRaw
  have rawBoth : (if Nat.beq run 2 then RestrictedInitialPolicy.DemandStarPolicy.emit d actual
      else RestrictedInitialPolicy.emit d actual) = some initial := by
    simp only [selectedRaw,ordinaryRaw,ite_self]
  have projected : scalar (fromInput actual) = actual := rfl
  have reachable : originalReach (fromInput actual) d.path = true := by
    unfold originalReach
    cases relation : dropPrefix (fromInput actual).path d.path with
    | none => rfl
    | some tail => cases tail <;> rfl
  have notBlocked : provisionalFlowExactBlocked d actual = false := rfl
  have valid : decide (2 ≤ run ∧ d.path.length ≤ m.fieldLimit ∧
      (fromInput actual).path.length ≤ m.fieldLimit) = true :=
    decide_eq_true ⟨restricted,budget,prefixFits⟩
  have legal : MayInitialToStarAudit.directionLegal m.direction initial = true := by
    cases m.direction <;> rfl
  have outputFits : decide (initial.path.length ≤ m.fieldLimit) = true := decide_eq_true budget
  have old : oldCell run m d (fromInput actual) = some (fromInput initial) := by
    unfold oldCell
    rw [projected,reachable,notBlocked,valid]
    simp only [Bool.true_and,Bool.not_false,if_true]
    rw [rawBoth]
    simp only [Option.bind_some,legal,outputFits,Bool.true_and,if_true]
    rfl
  have ordinaryBranch : c2 .starThenMayForAny run m d ⟨fromInput actual,.demand,false⟩ =
      ((oldCell run m d (fromInput actual)).map
        (answer ⟨fromInput actual,.demand,false⟩ (fromInput actual))).toList := rfl
  change c2 .starThenMayForAny run m d ⟨fromInput actual,.demand,false⟩ = _
  rw [ordinaryBranch,old]
  cases required <;> rfl

def certificateGuard (b : Nat) (path : List Acc) (mark : Mark) (s : Seed) : Bool :=
  decide (s.pattern = ⟨b,path,.starOrAny,mark,[]⟩ ∧ s.layer = intrinsicMark mark)
def labelSeeds (label : SelectedFullAdmission.Label) (seeds : List Seed) :
    List (SelectedFullAdmission.Label × Seed) := seeds.map (fun s => (label,s))

theorem certificate_keeps_complete_label_and_joint_answer_for_all_earlier_cuts
    (run : Nat) (m : Mode) (b : Nat) (path pre1 tail1 pre2 tail2 : List Acc)
    (required supplied : Mark) (label : SelectedFullAdmission.Label)
    (restricted : 2 ≤ run) (same1 : path = pre1 ++ tail1) (same2 : path = pre2 ++ tail2)
    (markMatches : RestrictedInitialPolicy.acceptsMark required supplied = true)
    (budget : path.length ≤ m.fieldLimit) :
    labelSeeds label (c2 .starThenMayForAny run m ⟨b,path,.any,required⟩
      ⟨fromInput (SelectedFullAdmission.mayAt b pre1 supplied),.demand,false⟩) =
    labelSeeds label (c2 .starThenMayForAny run m ⟨b,path,.any,required⟩
      ⟨fromInput (SelectedFullAdmission.mayAt b pre2 supplied),.demand,false⟩) ∧
    certificateGuard b path required ⟨⟨b,path,.starOrAny,required,[]⟩,intrinsicMark required⟩ = true := by
  have first := earlier_MAY_prefix_cut_emits_the_same_SOA_joint_seed run m b pre1 tail1 required supplied
    restricted markMatches (by simpa only [← same1] using budget)
  have second := earlier_MAY_prefix_cut_emits_the_same_SOA_joint_seed run m b pre2 tail2 required supplied
    restricted markMatches (by simpa only [← same2] using budget)
  rw [← same1] at first
  rw [← same2] at second
  exact ⟨by rw [first,second],by simp [certificateGuard]⟩

/-- DATA canonicalization is an input parameter, not a new DATA law. The literal
capability frontier is independent of its prefix coverage choices. -/
structure Point where
  dataRows : List Fact
  capabilityRows : List Fact
deriving DecidableEq, Repr

def isCapability (a : Fact) : Bool := marked a.pattern.head
def canonicalPoint (dataCanonical : List Fact → List Fact) (offered : List Fact) : Point :=
  ⟨dataCanonical (offered.map eraseFact),
    literalDedup (offered.filter isCapability)⟩
def guideEffect (run : Nat) (m : Mode) (d : RestrictedInitialPolicy.Demand)
    (offered : List Fact) (s : Seed) : Prop :=
  ∃ a, a ∈ offered ∧ isCapability a = true ∧ s ∈ c2 .starThenMayForAny run m d a
def retainedEffect (run : Nat) (m : Mode) (d : RestrictedInitialPolicy.Demand)
    (point : Point) (s : Seed) : Prop :=
  ∃ a, a ∈ point.capabilityRows ∧ s ∈ c2 .starThenMayForAny run m d a

theorem point_keeps_exact_pattern_layer_and_literal_H_coordinates
    (dataCanonical : List Fact → List Fact) (offered : List Fact) (a : Fact) :
    a ∈ (canonicalPoint dataCanonical offered).capabilityRows ↔
      a ∈ offered ∧ isCapability a = true := by
  change a ∈ literalDedup (offered.filter isCapability) ↔ _
  rw [exact_dedup_preserves_membership,List.mem_filter]

theorem capability_membership_is_independent_of_both_arrival_orders_and_duplicates
    (dataCanonical : List Fact → List Fact) (left right : List Fact) (a : Fact) :
    (a ∈ (canonicalPoint dataCanonical (left ++ right)).capabilityRows ↔
      a ∈ (canonicalPoint dataCanonical (right ++ left)).capabilityRows) ∧
    (a ∈ (canonicalPoint dataCanonical (left ++ left)).capabilityRows ↔
      a ∈ (canonicalPoint dataCanonical left).capabilityRows) := by
  simp only [point_keeps_exact_pattern_layer_and_literal_H_coordinates,List.mem_append,or_self]
  exact ⟨by rw [or_comm],True.intro⟩

theorem opaque_DATA_canonicalization_preserves_every_supplied_SOA_C2_effect
    (dataCanonical : List Fact → List Fact) (offered : List Fact)
    (run : Nat) (m : Mode) (d : RestrictedInitialPolicy.Demand) (s : Seed) :
    retainedEffect run m d (canonicalPoint dataCanonical offered) s ↔ guideEffect run m d offered s := by
  constructor
  · rintro ⟨a,member,emitted⟩
    obtain ⟨original,capability⟩ :=
      (point_keeps_exact_pattern_layer_and_literal_H_coordinates dataCanonical offered a).mp member
    exact ⟨a,original,capability,emitted⟩
  · rintro ⟨a,member,capability,emitted⟩
    exact ⟨a,(point_keeps_exact_pattern_layer_and_literal_H_coordinates dataCanonical offered a).mpr
      ⟨member,capability⟩,emitted⟩

theorem both_arrival_orders_keep_the_same_C2_capability_effects
    (dataCanonical : List Fact → List Fact) (left right : List Fact)
    (run : Nat) (m : Mode) (d : RestrictedInitialPolicy.Demand) (s : Seed) :
    retainedEffect run m d (canonicalPoint dataCanonical (left ++ right)) s ↔
      retainedEffect run m d (canonicalPoint dataCanonical (right ++ left)) s := by
  constructor
  · rintro ⟨a,member,emitted⟩
    exact ⟨a,(capability_membership_is_independent_of_both_arrival_orders_and_duplicates
      dataCanonical left right a).1.mp member,emitted⟩
  · rintro ⟨a,member,emitted⟩
    exact ⟨a,(capability_membership_is_independent_of_both_arrival_orders_and_duplicates
      dataCanonical left right a).1.mpr member,emitted⟩

theorem literal_H_and_layer_are_separate_capabilities_even_with_equal_geometry :
    let p := soa []
    let n : Fact := ⟨p,.normal,false⟩
    let protectedN : Fact := ⟨p,.normal,true⟩
    let demand : Fact := ⟨p,.demand,false⟩
    n ≠ protectedN ∧ n ≠ demand ∧
    (canonicalPoint (fun _ => []) [n,protectedN,demand]).capabilityRows = [n,protectedN,demand] := by decide

def check : Bool :=
  decide (normalizeND [soa [],plainStar [],soa []] = [plainStar []]) &&
  decide (certificateGuard 1 [] .flow ⟨soa [],.normal⟩ = true) &&
  decide (certificateGuard 1 [] .flow ⟨soa [],.demand⟩ = false) &&
  decide ((canonicalPoint (fun _ => []) [fact (plainStar []),fact (soa [])]).capabilityRows = [fact (soa [])])

theorem executable_supplement_cells : check = true := by decide
#eval (if check then "STAR_OR_ANY_OBLIGATIONS=true" else "STAR_OR_ANY_OBLIGATIONS=false")

#print axioms exact_dedup_preserves_membership
#print axioms normalized_ND_member_dedup_keeps_the_geometric_conjunction
#print axioms earlier_MAY_prefix_cut_emits_the_same_SOA_joint_seed
#print axioms certificate_keeps_complete_label_and_joint_answer_for_all_earlier_cuts
#print axioms point_keeps_exact_pattern_layer_and_literal_H_coordinates
#print axioms capability_membership_is_independent_of_both_arrival_orders_and_duplicates
#print axioms opaque_DATA_canonicalization_preserves_every_supplied_SOA_C2_effect
#print axioms both_arrival_orders_keep_the_same_C2_capability_effects
#print axioms literal_H_and_layer_are_separate_capabilities_even_with_equal_geometry
#print axioms executable_supplement_cells

end StarOrAnyObligations
