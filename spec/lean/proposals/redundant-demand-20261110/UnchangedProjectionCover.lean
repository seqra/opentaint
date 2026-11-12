import Std

/-!
Exact next-run guidance equality. Edge IDs denote complete raw outgoing
memberships. Projection coordinates denote complete normalized paired rows,
including the method/context/unit and physical ports. An injective native
encoding is a source-correspondence obligation, not display-name equality.

No transfer, subsumption or approximation rule is changed. Only a redundant
edge's contribution to the already selected guidance set is omitted.
-/
namespace UnchangedProjectionCover
set_option autoImplicit false

abbrev Edge := Nat

structure Projection where
  owner : Nat
  scope : Nat
  entryPort : Nat
  exitPort : Nat
  entry : Nat
  exit : Nat
  kind : Nat
  deriving DecidableEq, Repr

structure Witness where
  row : Projection
  anchor : Edge
  deriving Repr

structure Certificate where
  target : Edge
  witnesses : List Witness
  deriving Repr

/-- O is the complete later outgoing store; U is the complete fixed campaign
target set at that barrier. An anchor outside U is never retired by this campaign. -/
def validWitness (emit : Edge → List Projection) (O U : List Edge) (w : Witness) : Bool :=
  decide (w.anchor ∈ O) && decide (w.anchor ∉ U) && decide (w.row ∈ emit w.anchor)

def check (emit : Edge → List Projection) (O U : List Edge) (c : Certificate) : Bool :=
  decide (c.target ∈ O) && decide (c.target ∈ U) &&
    (emit c.target).all (fun q =>
      c.witnesses.any (fun w => decide (w.row = q) && validWitness emit O U w))

def checkAll (emit : Edge → List Projection) (O U Q : List Edge)
    (certificates : List Certificate) : Bool :=
  Q.all (fun e => certificates.any (fun c => decide (c.target = e) && check emit O U c))

/-- A finite injective native row dictionary can encode its complete JSON key
in one opaque coordinate. No short field, mark or port label is used. -/
def encodedRow (rank : Nat) : Projection := ⟨rank, 0, 0, 0, 0, 0, 0⟩

theorem encodedRow_injective (a b : Nat) (h : encodedRow a = encodedRow b) : a = b := by
  exact congrArg Projection.owner h

/-- Only captured known edges are overridden. Every other edge retains an
arbitrary emission supplied by the caller, rather than an invented empty row. -/
def withKnownRows (known : List (Edge × List Projection))
    (rest : Edge → List Projection) (e : Edge) : List Projection :=
  (known.lookup e).getD (rest e)

theorem withKnownRows_of_lookup (known : List (Edge × List Projection))
    (rest : Edge → List Projection) (e : Edge) (qs : List Projection)
    (h : known.lookup e = some qs) : withKnownRows known rest e = qs := by
  simp [withKnownRows, h]

theorem withKnownRows_outside_known (known : List (Edge × List Projection))
    (rest : Edge → List Projection) (e : Edge) (h : known.lookup e = none) :
    withKnownRows known rest e = rest e := by
  simp [withKnownRows, h]

def without (O removed : List Edge) : List Edge :=
  O.filter (fun e => decide (e ∉ removed))

def HasProjection (emit : Edge → List Projection) (O : List Edge) (q : Projection) : Prop :=
  ∃ e ∈ O, q ∈ emit e

/-- An executable demand lookup. Its equality is stronger than equal finding counts. -/
def lookup (emit : Edge → List Projection) (O : List Edge) (q : Projection) : Bool :=
  O.any (fun e => decide (q ∈ emit e))

theorem mem_without (O removed : List Edge) (e : Edge) :
    e ∈ without O removed ↔ e ∈ O ∧ e ∉ removed := by
  simp [without]

theorem lookup_true_iff (emit : Edge → List Projection) (O : List Edge) (q : Projection) :
    lookup emit O q = true ↔ HasProjection emit O q := by
  simp [lookup, HasProjection, List.any_eq_true]

theorem checked_witness (emit : Edge → List Projection) (O U : List Edge) (w : Witness)
    (h : validWitness emit O U w = true) :
    w.anchor ∈ O ∧ w.anchor ∉ U ∧ w.row ∈ emit w.anchor := by
  simpa [validWitness, Bool.and_eq_true, and_assoc] using h

theorem witness_checked_of_memberships (emit : Edge → List Projection) (O U : List Edge)
    (w : Witness) (ho : w.anchor ∈ O) (hu : w.anchor ∉ U) (hq : w.row ∈ emit w.anchor) :
    validWitness emit O U w = true := by
  simp [validWitness, ho, hu, hq]

theorem certificate_checked_of_witnesses (emit : Edge → List Projection) (O U : List Edge)
    (c : Certificate) (ho : c.target ∈ O) (hu : c.target ∈ U)
    (h : ∀ q ∈ emit c.target,
      ∃ w ∈ c.witnesses, w.row = q ∧ validWitness emit O U w = true) :
    check emit O U c = true := by
  simpa only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true] using And.intro (And.intro ho hu) h

theorem checkAll_mapped_targets (emit : Edge → List Projection) (O U : List Edge)
    (certificates : List Certificate) (h : ∀ c ∈ certificates, check emit O U c = true) :
    checkAll emit O U (certificates.map Certificate.target) certificates = true := by
  simp only [checkAll, List.all_eq_true]
  intro e he
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨c, hc, rfl, h c hc⟩

theorem checked_target_membership (emit : Edge → List Projection) (O U : List Edge)
    (c : Certificate) (h : check emit O U c = true) : c.target ∈ O ∧ c.target ∈ U := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- Every covered row yields a concrete anchor selected from the supplied certificate. -/
theorem checked_row_has_witness (emit : Edge → List Projection) (O U : List Edge)
    (c : Certificate) (h : check emit O U c = true) (q : Projection)
    (hq : q ∈ emit c.target) :
    ∃ w ∈ c.witnesses, w.row = q ∧ w.anchor ∈ O ∧ w.anchor ∉ U ∧ q ∈ emit w.anchor := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have one := h.2 q hq
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at one
  obtain ⟨w, hw, heq, valid⟩ := one
  obtain ⟨ho, hu, hr⟩ := checked_witness emit O U w valid
  exact ⟨w, hw, heq, ho, hu, by simpa [heq] using hr⟩

theorem checked_all_has_certificate (emit : Edge → List Projection) (O U Q : List Edge)
    (certificates : List Certificate) (h : checkAll emit O U Q certificates = true)
    (e : Edge) (he : e ∈ Q) :
    ∃ c ∈ certificates, c.target = e ∧ check emit O U c = true := by
  simp only [checkAll, List.all_eq_true] at h
  have one := h e he
  simpa only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] using one

theorem checked_all_subset (emit : Edge → List Projection) (O U Q : List Edge)
    (certificates : List Certificate) (h : checkAll emit O U Q certificates = true) :
    ∀ e ∈ Q, e ∈ U := by
  intro e he
  obtain ⟨c, _, hc, valid⟩ := checked_all_has_certificate emit O U Q certificates h e he
  have member := (checked_target_membership emit O U c valid).2
  simpa [hc] using member

theorem checked_anchor_survives (emit : Edge → List Projection) (O U R Q : List Edge)
    (certificates : List Certificate) (h : checkAll emit O U Q certificates = true)
    (hR : ∀ e ∈ R, e ∈ U) (anchor : Edge) (ho : anchor ∈ O) (hu : anchor ∉ U) :
    anchor ∈ without (without O R) Q := by
  apply (mem_without (without O R) Q anchor).2
  constructor
  · apply (mem_without O R anchor).2
    exact ⟨ho, fun hr => hu (hR anchor hr)⟩
  · intro hq
    exact hu (checked_all_subset emit O U Q certificates h anchor hq)

/-- Joint deletion is safe even when other accepted retirements have removed
an arbitrary subset R of U. There is no disjointness assumption or circular support. -/
theorem projection_set_unchanged (emit : Edge → List Projection) (O U R Q : List Edge)
    (certificates : List Certificate) (h : checkAll emit O U Q certificates = true)
    (hR : ∀ e ∈ R, e ∈ U) (q : Projection) :
    HasProjection emit (without (without O R) Q) q ↔ HasProjection emit (without O R) q := by
  constructor
  · rintro ⟨e, he, hr⟩
    exact ⟨e, ((mem_without (without O R) Q e).1 he).1, hr⟩
  · rintro ⟨e, he, hr⟩
    by_cases removed : e ∈ Q
    · obtain ⟨c, _, hc, valid⟩ := checked_all_has_certificate emit O U Q certificates h e removed
      have row : q ∈ emit c.target := by simpa [hc] using hr
      obtain ⟨w, _, _, ho, hu, hw⟩ := checked_row_has_witness emit O U c valid q row
      exact ⟨w.anchor, checked_anchor_survives emit O U R Q certificates h hR w.anchor ho hu, hw⟩
    · exact ⟨e, (mem_without (without O R) Q e).2 ⟨he, removed⟩, hr⟩

theorem lookup_unchanged (emit : Edge → List Projection) (O U R Q : List Edge)
    (certificates : List Certificate) (h : checkAll emit O U Q certificates = true)
    (hR : ∀ e ∈ R, e ∈ U) (q : Projection) :
    lookup emit (without (without O R) Q) q = lookup emit (without O R) q := by
  have iffTrue : lookup emit (without (without O R) Q) q = true ↔
      lookup emit (without O R) q = true := by
    rw [lookup_true_iff, lookup_true_iff]
    exact projection_set_unchanged emit O U R Q certificates h hR q
  cases a : lookup emit (without (without O R) Q) q <;>
    cases b : lookup emit (without O R) q <;> simp_all

/-- The stable component contains the untouched raw stores, native NORMAL
records, reports, seeds, source hits and other state required by the next run.
Diagnostic callback counts and allocation IDs are not semantic guidance. -/
abbrev State (Stable : Type) := Stable × (Projection → Bool)

def buildState {Stable : Type} (stable : Stable) (emit : Edge → List Projection)
    (O : List Edge) : State Stable := (stable, lookup emit O)

theorem semantic_state_unchanged {Stable : Type} (stable : Stable)
    (emit : Edge → List Projection) (O U R Q : List Edge)
    (certificates : List Certificate) (h : checkAll emit O U Q certificates = true)
    (hR : ∀ e ∈ R, e ∈ U) :
    buildState stable emit (without (without O R) Q) = buildState stable emit (without O R) := by
  have same : lookup emit (without (without O R) Q) = lookup emit (without O R) := by
    funext q
    exact lookup_unchanged emit O U R Q certificates h hR q
  exact congrArg (fun demand => (stable, demand)) same

def run {S : Type} (step : S → S) : Nat → S → S
  | 0, s => s
  | n + 1, s => run step n (step s)

theorem all_future_states_unchanged {Stable : Type} (stable : Stable)
    (emit : Edge → List Projection) (O U R Q : List Edge)
    (certificates : List Certificate) (h : checkAll emit O U Q certificates = true)
    (hR : ∀ e ∈ R, e ∈ U) (step : State Stable → State Stable) (n : Nat) :
    run step n (buildState stable emit (without (without O R) Q)) =
      run step n (buildState stable emit (without O R)) := by
  exact congrArg (run step n) (semantic_state_unchanged stable emit O U R Q certificates h hR)

theorem future_observations_unchanged {Stable Observation : Type} (stable : Stable)
    (emit : Edge → List Projection) (O U R Q : List Edge)
    (certificates : List Certificate) (h : checkAll emit O U Q certificates = true)
    (hR : ∀ e ∈ R, e ∈ U) (step : State Stable → State Stable)
    (observe : State Stable → Observation) (n : Nat) :
    observe (run step n (buildState stable emit (without (without O R) Q))) =
      observe (run step n (buildState stable emit (without O R))) := by
  exact congrArg observe (all_future_states_unchanged stable emit O U R Q certificates h hR step n)

/-- A finite trace also permits nondeterministic scheduling of the same semantic state. -/
inductive Follows {S : Type} (step : S → S → Prop) : S → List S → Prop where
  | done (s : S) : Follows step s []
  | next {s t : S} {rest : List S} : step s t → Follows step t rest → Follows step s (t :: rest)

theorem all_future_traces_unchanged {Stable : Type} (stable : Stable)
    (emit : Edge → List Projection) (O U R Q : List Edge)
    (certificates : List Certificate) (h : checkAll emit O U Q certificates = true)
    (hR : ∀ e ∈ R, e ∈ U) (step : State Stable → State Stable → Prop)
    (trace : List (State Stable)) :
    Follows step (buildState stable emit (without (without O R) Q)) trace ↔
      Follows step (buildState stable emit (without O R)) trace := by
  rw [semantic_state_unchanged stable emit O U R Q certificates h hR]

/-! Executable positive and negative examples. They are finite proof fixtures,
not project deletion controls or source-completeness claims. -/
def q1 : Projection := ⟨0, 0, 0, 0, 10, 20, 0⟩
def q2 : Projection := ⟨0, 0, 0, 0, 11, 20, 0⟩
def wrongPort : Projection := { q1 with exitPort := 1 }
def otherExit : Projection := { q1 with exit := 21 }
def otherEntry : Projection := { q1 with entry := 12 }

def oneRow (e : Edge) : List Projection := if e = 1 ∨ e = 2 then [q1] else []
def twoRows (e : Edge) : List Projection := if e = 1 then [q1, q2] else if e = 2 then [q1] else []
def portRows (e : Edge) : List Projection := if e = 1 then [q1] else if e = 2 then [wrongPort] else []
def mixedPairRows (e : Edge) : List Projection :=
  if e = 1 then [q1] else if e = 2 then [otherExit] else if e = 3 then [otherEntry] else []
def c1 : Certificate := ⟨1, [⟨q1, 2⟩]⟩

theorem retained_anchor_example : checkAll oneRow [1, 2] [1] [1] [c1] = true := by decide
theorem duplicate_projection_occurrences_example :
    check (fun e => if e = 1 then [q1, q1] else [q1]) [1, 2] [1] c1 = true := by decide
theorem empty_projection_example : check (fun _ => []) [1] [1] ⟨1, []⟩ = true := by decide

theorem circular_anchor_rejected : check oneRow [1, 2] [1, 2] c1 = false := by decide
theorem circular_deletion_loses_row :
    lookup oneRow [1, 2] q1 = true ∧ lookup oneRow (without [1, 2] [1, 2]) q1 = false := by decide
theorem other_retirement_anchor_rejected : check oneRow [1, 2] [1, 2] c1 = false := by decide
theorem deleting_other_anchor_then_target_loses_row :
    lookup oneRow (without [1, 2] [2]) q1 = true ∧
      lookup oneRow (without (without [1, 2] [2]) [1]) q1 = false := by decide
theorem one_of_two_nd_rows_is_insufficient : check twoRows [1, 2] [1] c1 = false := by decide
theorem missing_nd_row_is_lost :
    lookup twoRows [1, 2] q2 = true ∧ lookup twoRows (without [1, 2] [1]) q2 = false := by decide
theorem wrong_port_anchor_rejected : check portRows [1, 2] [1] c1 = false := by decide
theorem wrong_port_is_a_different_row : q1 ≠ wrongPort := by decide
theorem independently_matched_endpoints_are_insufficient :
    check mixedPairRows [1, 2, 3] [1] ⟨1, [⟨q1, 2⟩, ⟨q1, 3⟩]⟩ = false := by decide
theorem absent_anchor_rejected : check oneRow [1] [1] c1 = false := by decide
theorem target_outside_U_rejected : check oneRow [1, 2] [] c1 = false := by decide

#print axioms projection_set_unchanged
#print axioms semantic_state_unchanged
#print axioms all_future_states_unchanged
#print axioms future_observations_unchanged
#print axioms all_future_traces_unchanged
end UnchangedProjectionCover
