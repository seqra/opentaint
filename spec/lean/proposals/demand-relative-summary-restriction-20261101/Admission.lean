import Init

/-!
Constructive operational admission model. Geometry and exact paired restriction
are parameters, not assumed properties of the store. The executable `restrict`
function is called before membership/dedup; raw candidates have no state field.

The model has only the semantic row set and a publication queue. Native records,
next-run demand and provider indexes are views of that admitted set. It does not
claim the supplied geometry/coverage predicates are sound, or prove whole-program
finding completeness. Those are separate obligations.
-/
namespace RelativeRestriction.Admission
set_option autoImplicit false

inductive Layer where
  | normal | demand
  deriving DecidableEq, Repr

structure State (E : Type) where
  rows : List E := []
  pending : List E := []
  deriving Repr

variable {E Raw : Type} [DecidableEq E]

/-- Same final annotated membership only: the caller must include all semantic
metadata, including protection, in E or give a separately proved merge adapter. -/
def insert (s : State E) (e : E) : State E :=
  if e ∈ s.rows then s else ⟨s.rows ++ [e], s.pending ++ [e]⟩

def addPieces : State E → List E → State E
  | s, [] => s
  | s, e :: es => addPieces (insert s e) es

/-- There is deliberately no admission of `raw` before the restriction call. -/
def offer (restrict : Raw → List E) (s : State E) (raw : Raw) : State E :=
  addPieces s (restrict raw)

def flush (s : State E) : State E := ⟨s.rows, []⟩

def native (layer : E → Layer) (eligible : E → Bool) (s : State E) : List E :=
  s.rows.filter (fun e => layer e == .normal && eligible e)

def frontier (layer : E → Layer) (s : State E) : List E :=
  s.rows.filter (fun e => layer e == .demand)

/-- An index has no independent candidate insertion path. -/
def index (select : E → Bool) (s : State E) : List E := s.rows.filter select

/-- NORMAL-provider scope only. Coverage is intentionally external: this file
proves admission provenance, not AP-geometric replacement correctness. Existing
admitted DEMAND-to-DEMAND providers are outside this view and are not forbidden. -/
def providers (layer : E → Layer) (flow covers : E → Bool) (s : State E) : List E :=
  s.rows.filter (fun e => layer e == .normal && flow e && covers e)

theorem mem_insert_rows (s : State E) (e x : E) :
    x ∈ (insert s e).rows ↔ x ∈ s.rows ∨ x = e := by
  unfold insert
  split
  · rename_i seen
    constructor
    · exact fun h => Or.inl h
    · intro h
      rcases h with h | rfl
      · exact h
      · exact seen
  · simp only [List.mem_append, List.mem_singleton]

theorem mem_addPieces_rows (s : State E) (es : List E) (x : E) :
    x ∈ (addPieces s es).rows ↔ x ∈ s.rows ∨ x ∈ es := by
  induction es generalizing s with
  | nil => simp [addPieces]
  | cons e es ih =>
    simp only [addPieces, ih, mem_insert_rows, List.mem_cons]
    constructor
    · intro h
      rcases h with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · intro h
      rcases h with h | (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem mem_offer_rows (restrict : Raw → List E) (s : State E) (raw : Raw) (x : E) :
    x ∈ (offer restrict s raw).rows ↔ x ∈ s.rows ∨ x ∈ restrict raw :=
  mem_addPieces_rows s (restrict raw) x

theorem rejected_changes_no_state (restrict : Raw → List E) (s : State E) (raw : Raw)
    (rejected : restrict raw = []) : offer restrict s raw = s := by
  simp only [offer, rejected, addPieces]

theorem duplicate_changes_no_state (s : State E) (e : E) (seen : e ∈ s.rows) :
    insert s e = s := by simp only [insert, if_pos seen]

theorem pending_insert_is_admitted (s : State E)
    (valid : ∀ x ∈ s.pending, x ∈ s.rows) (e : E) :
    ∀ x ∈ (insert s e).pending, x ∈ (insert s e).rows := by
  unfold insert
  split
  · exact valid
  · intro x h
    simp only [List.mem_append, List.mem_singleton] at h ⊢
    rcases h with h | h
    · exact Or.inl (valid x h)
    · exact Or.inr h

theorem pending_addPieces_is_admitted (s : State E)
    (valid : ∀ x ∈ s.pending, x ∈ s.rows) (es : List E) :
    ∀ x ∈ (addPieces s es).pending, x ∈ (addPieces s es).rows := by
  induction es generalizing s with
  | nil => exact valid
  | cons e es ih =>
    exact ih (insert s e) (pending_insert_is_admitted s valid e)

omit [DecidableEq E] in
theorem native_is_admitted (layer : E → Layer) (eligible : E → Bool) (s : State E)
    (e : E) (h : e ∈ native layer eligible s) : e ∈ s.rows :=
  (List.mem_filter.mp h).1

omit [DecidableEq E] in
theorem frontier_is_admitted (layer : E → Layer) (s : State E) (e : E)
    (h : e ∈ frontier layer s) : e ∈ s.rows := (List.mem_filter.mp h).1

omit [DecidableEq E] in
theorem index_is_admitted (select : E → Bool) (s : State E) (e : E)
    (h : e ∈ index select s) : e ∈ s.rows := (List.mem_filter.mp h).1

omit [DecidableEq E] in
theorem frontier_classifies_final_layer (layer : E → Layer) (s : State E) (e : E) :
    e ∈ frontier layer s ↔ e ∈ s.rows ∧ layer e = .demand := by
  simp [frontier]

omit [DecidableEq E] in
theorem native_classifies_final_layer (layer : E → Layer) (eligible : E → Bool)
    (s : State E) (e : E) : e ∈ native layer eligible s ↔
      e ∈ s.rows ∧ layer e = .normal ∧ eligible e = true := by
  simp [native, Bool.and_eq_true]

/-- A barrier extends the earlier immutable record snapshot with eligible
admitted NORMAL rows. It has no raw-candidate input channel. -/
def persist (old : List E) (layer : E → Layer) (eligible : E → Bool)
    (s : State E) : List E := old ++ native layer eligible s

omit [DecidableEq E] in
theorem newly_persisted_is_admitted (old : List E) (layer : E → Layer)
    (eligible : E → Bool) (s : State E) (e : E)
    (stored : e ∈ persist old layer eligible s) (new : e ∉ old) : e ∈ s.rows := by
  rcases List.mem_append.mp stored with existing | added
  · exact False.elim (new existing)
  · exact native_is_admitted layer eligible s e added

/-- NORMAL input classification is not reused after restriction. -/
theorem normal_candidate_cut_to_demand_is_guidance
    (restrict : Raw → List E) (layer : E → Layer) (s : State E) (raw : Raw) (e : E)
    (cut : e ∈ restrict raw) (finalLayer : layer e = .demand) :
    e ∈ frontier layer (offer restrict s raw) := by
  exact (frontier_classifies_final_layer layer _ e).mpr
    ⟨(mem_offer_rows restrict s raw e).mpr (Or.inr cut), finalLayer⟩

theorem normal_candidate_cut_to_demand_is_not_native
    (restrict : Raw → List E) (layer : E → Layer) (eligible : E → Bool)
    (s : State E) (raw : Raw) (e : E) (finalLayer : layer e = .demand) :
    e ∉ native layer eligible (offer restrict s raw) := by
  intro h
  have n := ((native_classifies_final_layer layer eligible _ e).mp h).2.1
  rw [finalLayer] at n
  cases n

omit [DecidableEq E] in
theorem provider_passed_admission (layer : E → Layer) (flow covers : E → Bool)
    (s : State E) (e : E) (h : e ∈ providers layer flow covers s) :
    e ∈ s.rows ∧ layer e = .normal ∧ flow e = true ∧ covers e = true := by
  simpa [providers, Bool.and_eq_true, and_assoc] using h

/-- Finite execution history is an external proof trace, not an analyzer raw cache. -/
inductive Trace (restrict : Raw → List E) : List Raw → State E → Prop
  | empty : Trace restrict [] ⟨[], []⟩
  | offered {history : List Raw} {s : State E} (previous : Trace restrict history s)
      (raw : Raw) : Trace restrict (history ++ [raw]) (offer restrict s raw)
  | flushed {history : List Raw} {s : State E} (previous : Trace restrict history s) :
      Trace restrict history (flush s)

/-- Every semantic row has an actual earlier restriction-output witness. The proof
constructs the raw witness from the finite trace; it never assumes provenance. -/
theorem reachable_rows_have_gate_provenance (restrict : Raw → List E)
    (history : List Raw) (s : State E) (trace : Trace restrict history s) :
    ∀ e ∈ s.rows, ∃ raw, raw ∈ history ∧ e ∈ restrict raw := by
  induction trace with
  | empty => simp
  | @offered history s prior raw ih =>
    intro e h
    rcases (mem_offer_rows restrict s raw e).mp h with old | fresh
    · obtain ⟨r, hr, he⟩ := ih e old
      exact ⟨r, List.mem_append_left _ hr, he⟩
    · exact ⟨raw, List.mem_append_right _ (by simp), fresh⟩
  | @flushed history s prior ih => exact ih

theorem reachable_publications_have_gate_provenance (restrict : Raw → List E)
    (history : List Raw) (s : State E) (trace : Trace restrict history s) :
    ∀ e ∈ s.pending, e ∈ s.rows := by
  induction trace with
  | empty => simp
  | @offered history s prior raw ih =>
    exact pending_addPieces_is_admitted s ih (restrict raw)
  | @flushed history s prior ih => simp [flush]

theorem reachable_native_has_gate_witness (restrict : Raw → List E)
    (layer : E → Layer) (eligible : E → Bool) (history : List Raw) (s : State E)
    (trace : Trace restrict history s) (e : E) (h : e ∈ native layer eligible s) :
    ∃ raw, raw ∈ history ∧ e ∈ restrict raw :=
  reachable_rows_have_gate_provenance restrict history s trace e
    (native_is_admitted layer eligible s e h)

theorem reachable_provider_has_gate_witness (restrict : Raw → List E)
    (layer : E → Layer) (flow covers : E → Bool) (history : List Raw) (s : State E)
    (trace : Trace restrict history s) (e : E) (h : e ∈ providers layer flow covers s) :
    ∃ raw, raw ∈ history ∧ e ∈ restrict raw :=
  reachable_rows_have_gate_provenance restrict history s trace e
    (provider_passed_admission layer flow covers s e h).1

/-- Executable provenance lookup over the external finite proof trace. No
choice axiom, unbounded search, or analyzer raw-state store is involved. -/
def source? (restrict : Raw → List E) (e : E) : List Raw → Option Raw
  | [] => none
  | raw :: history => if e ∈ restrict raw then some raw else source? restrict e history

theorem source_is_some_of_gate_witness (restrict : Raw → List E) (e : E)
    (history : List Raw) (witness : ∃ raw, raw ∈ history ∧ e ∈ restrict raw) :
    (source? restrict e history).isSome = true := by
  induction history with
  | nil => simp at witness
  | cons raw history ih =>
    unfold source?
    split
    · rfl
    · rename_i absent
      apply ih
      obtain ⟨r, member, gate⟩ := witness
      rcases List.mem_cons.mp member with same | later
      · subst r
        exact False.elim (absent gate)
      · exact ⟨r, later, gate⟩

theorem source_lookup_sound (restrict : Raw → List E) (e : E) (history : List Raw)
    (raw : Raw) (found : source? restrict e history = some raw) :
    raw ∈ history ∧ e ∈ restrict raw := by
  induction history with
  | nil => simp [source?] at found
  | cons r history ih =>
    unfold source? at found
    split at found
    · rename_i gate
      have same := Option.some.inj found
      subst raw
      exact ⟨List.mem_cons_self, gate⟩
    · obtain ⟨member, gate⟩ := ih found
      exact ⟨List.mem_cons_of_mem r member, gate⟩

theorem reachable_row_has_executable_receipt (restrict : Raw → List E)
    (history : List Raw) (s : State E) (trace : Trace restrict history s)
    (e : E) (admitted : e ∈ s.rows) :
    (source? restrict e history).isSome = true :=
  source_is_some_of_gate_witness restrict e history
    (reachable_rows_have_gate_provenance restrict history s trace e admitted)

theorem reachable_pending_has_gate_witness (restrict : Raw → List E)
    (history : List Raw) (s : State E) (trace : Trace restrict history s)
    (e : E) (h : e ∈ s.pending) : ∃ raw, raw ∈ history ∧ e ∈ restrict raw :=
  reachable_rows_have_gate_provenance restrict history s trace e
    (reachable_publications_have_gate_provenance restrict history s trace e h)

theorem reachable_frontier_has_gate_witness (restrict : Raw → List E)
    (layer : E → Layer) (history : List Raw) (s : State E)
    (trace : Trace restrict history s) (e : E) (h : e ∈ frontier layer s) :
    ∃ raw, raw ∈ history ∧ e ∈ restrict raw :=
  reachable_rows_have_gate_provenance restrict history s trace e
    (frontier_is_admitted layer s e h)

theorem reachable_index_has_gate_witness (restrict : Raw → List E)
    (select : E → Bool) (history : List Raw) (s : State E)
    (trace : Trace restrict history s) (e : E) (h : e ∈ index select s) :
    ∃ raw, raw ∈ history ∧ e ∈ restrict raw :=
  reachable_rows_have_gate_provenance restrict history s trace e
    (index_is_admitted select s e h)

/- Concrete transition controls expose the old raw-layer classification error
and a rejected FLOW candidate which cannot enter the NORMAL-provider index. -/
namespace Controls
structure Edge where
  key : Nat
  layer : Layer
  flow : Bool
  protection : Bool
  deriving DecidableEq, Repr

def rawNormal : Edge := ⟨1, .normal, true, true⟩
def cutDemand : Edge := ⟨2, .demand, true, true⟩
def rejectedFlow : Edge := ⟨3, .normal, true, false⟩
def gate (raw : Edge) : List Edge :=
  if raw = rawNormal then [cutDemand] else []

theorem normal_raw_is_not_semantically_admitted :
    (offer gate ⟨[], []⟩ rawNormal).rows = [cutDemand] := by decide

theorem normal_raw_produces_demand_and_no_native :
    frontier Edge.layer (offer gate ⟨[], []⟩ rawNormal) = [cutDemand] ∧
      native Edge.layer (fun _ => true) (offer gate ⟨[], []⟩ rawNormal) = [] := by decide

theorem normal_flow_cut_to_demand_cannot_be_a_normal_provider :
    providers Edge.layer Edge.flow (fun _ => true)
      (offer gate ⟨[], []⟩ rawNormal) = [] := by decide

theorem rejected_flow_cannot_be_a_provider :
    providers Edge.layer Edge.flow (fun _ => true)
      (offer gate ⟨[], []⟩ rejectedFlow) = [] := by decide

theorem published_cut_keeps_protection :
    (offer gate ⟨[], []⟩ rawNormal).pending = [⟨2, .demand, true, true⟩] := by decide

end Controls

#print axioms rejected_changes_no_state
#print axioms reachable_rows_have_gate_provenance
#print axioms reachable_native_has_gate_witness
#print axioms reachable_provider_has_gate_witness
#print axioms normal_candidate_cut_to_demand_is_guidance
#print axioms reachable_row_has_executable_receipt
#print axioms Controls.normal_raw_produces_demand_and_no_native
#print axioms Controls.rejected_flow_cannot_be_a_provider
end RelativeRestriction.Admission
