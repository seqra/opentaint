import Std

namespace ExactMayEmission

abbrev Path := List Nat
inductive Tail where | exact | may | must | star
  deriving DecidableEq, Repr
inductive Mark where | flow | full (id : Nat)
  deriving DecidableEq, Repr
structure Fact where
  path : Path
  tail : Tail
  mark : Mark
  demand : Bool := false
  deriving DecidableEq, Repr
structure Guide where
  path : Path
  tail : Tail
  mark : Mark
  mayEmpty : Bool := true
  deriving DecidableEq, Repr
structure Seed where
  path : Path
  tail : Tail
  mark : Mark
  demand : Bool
  deriving DecidableEq, Repr

def dropPrefix : Path → Path → Option Path
  | [], rest => some rest
  | _ :: _, [] => none
  | p :: ps, a :: xs => if p = a then dropPrefix ps xs else none

theorem dropPrefix_sound (p q suffix : Path) (h : dropPrefix p q = some suffix) :
    q = p ++ suffix := by
  induction p generalizing q with
  | nil => cases h; rfl
  | cons first rest ih =>
    cases q with
    | nil => cases h
    | cons a tail =>
      simp only [dropPrefix] at h
      split at h
      · rename_i same
        subst a
        have tailEq := ih tail h
        rw [tailEq]
        rfl
      · cases h

def under (head word : Path) : Prop := ∃ suffix, word = head ++ suffix

theorem first_field_may_view_covers_all_original_bindings
    (p q : Path) (f : Nat) (rest suffix : Path)
    (h : dropPrefix p q = some (f :: rest)) :
    under (p ++ [f]) (q ++ suffix) := by
  have shape := dropPrefix_sound p q (f :: rest) h
  refine ⟨rest ++ suffix,?_⟩
  rw [shape]
  simp only [List.append_assoc,List.singleton_append]
  rfl

theorem deeper_demand_may_view_stays_inside_original_may
    (q p extension suffix : Path) (h : dropPrefix q p = some extension) :
    under q (p ++ suffix) := by
  refine ⟨extension ++ suffix,?_⟩
  rw [dropPrefix_sound q p extension h]
  exact List.append_assoc q extension suffix

def compatible : Mark → Mark → Bool
  | .flow, _ => true
  | .full t, .full u => decide (t = u)
  | _, _ => false

inductive Choice where
  | point (path : Path)
  | uncertain (path : Path)
  | uniform (path : Path)
  deriving DecidableEq, Repr

-- The model factors unchanged base, static-anchor, E and field-budget
-- guards out of this spatial selector. MUST needs a forward-run guard.
def choose (run : Nat) (d : Guide) (a : Fact) : Option Choice :=
  if !compatible d.mark a.mark || a.tail = .star || d.tail = .must then none
  else if d.path = a.path then
    match d.tail,a.tail with
    | .may,.exact => if d.mayEmpty then some (.point d.path) else none
    | .may,.may => some (.uncertain d.path)
    | .may,.must => some (.uniform d.path)
    | .exact,.may => match d.mark with | .flow => none | _ => some (.point d.path)
    | .star,_ | .exact,_ => some (.point d.path)
    | _,_ => none
  else match dropPrefix d.path a.path with
    | some (f :: _) => match d.tail with
      | .may =>
        let p := d.path ++ [f]
        if a.tail = .exact ∧ a.path = p then some (.point p)
        else some (.uncertain p)
      | .star => if run = 2 then some (.uncertain d.path) else none
      | _ => none
    | _ => match dropPrefix a.path d.path,a.tail with
      | some (_ :: _),.may => match d.tail,d.mark with
        | .may,_ => some (.uncertain d.path)
        | .exact,.flow => none
        | .exact,_ | .star,_ => some (.point d.path)
        | _,_ => none
      | some (_ :: _),.must => match d.tail with
        | .may => some (.uniform d.path)
        | .star | .exact => some (.point d.path)
        | _ => none
      | _,_ => none

def pointDemand (m : Mark) (a : Fact) : Bool :=
  match m with | .flow => false | _ => a.demand || decide (a.tail = .may)

def probe (p : Path) : Seed := ⟨p,.exact,.flow,false⟩
def family (d : Guide) (a : Fact) : Choice → List Seed
  | .point p => [⟨p,.exact,d.mark,pointDemand d.mark a⟩]
  | .uncertain p => [probe p,⟨p,.may,d.mark,true⟩]
  | .uniform p => [⟨p,.must,d.mark,match d.mark with | .flow => false | _ => a.demand⟩]

def emit (run : Nat) (d : Guide) (a : Fact) : List Seed :=
  match choose run d a with
  | none => []
  | some selected =>
    let primary := family d a selected
    -- Keep the existing successful proper-descendant FLOW prefix probe.
    match d.tail,dropPrefix d.path a.path with
    | .may,some (_ :: _) => primary ++ [probe d.path]
    | _,_ => primary

theorem family_has_no_star (d : Guide) (a : Fact) (c : Choice)
    (s : Seed) (h : s ∈ family d a c) : s.tail ≠ .star := by
  cases c with
  | point p =>
    rcases List.mem_cons.mp h with rfl | impossible
    · change Tail.exact ≠ Tail.star; decide
    · cases impossible
  | uncertain p =>
    rcases List.mem_cons.mp h with rfl | more
    · change Tail.exact ≠ Tail.star; decide
    · rcases List.mem_cons.mp more with rfl | impossible
      · change Tail.may ≠ Tail.star; decide
      · cases impossible
  | uniform p =>
    rcases List.mem_cons.mp h with rfl | impossible
    · change Tail.must ≠ Tail.star; decide
    · cases impossible

theorem may_family_is_demand (d : Guide) (a : Fact) (c : Choice)
    (s : Seed) (h : s ∈ family d a c) (may : s.tail = .may) : s.demand = true := by
  cases c with
  | point p =>
    rcases List.mem_cons.mp h with rfl | impossible
    · cases may
    · cases impossible
  | uncertain p =>
    rcases List.mem_cons.mp h with rfl | more
    · cases may
    · rcases List.mem_cons.mp more with rfl | impossible
      · rfl
      · cases impossible
  | uniform p =>
    rcases List.mem_cons.mp h with rfl | impossible
    · cases may
    · cases impossible

theorem emitted_initial_has_no_star (run : Nat) (d : Guide) (a : Fact)
    (s : Seed) (member : s ∈ emit run d a) : s.tail ≠ .star := by
  unfold emit at member
  cases hc : choose run d a with
  | none => simp only [hc,List.not_mem_nil] at member
  | some c =>
    simp only [hc] at member
    cases ht : d.tail <;> cases hp : dropPrefix d.path a.path <;>
      simp only [ht,hp] at member
    all_goals first
    | exact family_has_no_star d a c s member
    | rename_i suffix
      cases suffix with
      | nil => exact family_has_no_star d a c s member
      | cons field rest =>
        rcases List.mem_append.mp member with main | extra
        · exact family_has_no_star d a c s main
        · rcases List.mem_cons.mp extra with rfl | impossible
          · change Tail.exact ≠ Tail.star; decide
          · cases impossible

def storedSeed (s : Seed) : Seed :=
  match s.mark,s.tail with
  | .flow,.exact => {s with tail := .star}
  | _,_ => s
def storedImage (run : Nat) (d : Guide) (a : Fact) : List Seed :=
  (emit run d a).map storedSeed

theorem stored_image_has_executable_raw_witness (run : Nat) (d : Guide)
    (a : Fact) (key : Seed) (h : key ∈ storedImage run d a) :
    ∃ raw, raw ∈ emit run d a ∧ storedSeed raw = key := by
  exact List.mem_map.mp h

def rootGuide : Guide := ⟨[],.may,.flow,true⟩
def fullT : Mark := .full 1

theorem same_head_may_has_exact_probe_and_may :
    emit 3 rootGuide ⟨[],.may,fullT,true⟩ =
      [⟨[],.exact,.flow,false⟩,⟨[],.may,.flow,true⟩] := by decide

theorem explicit_first_field_example :
    emit 3 rootGuide ⟨[1,2,3],.may,fullT,true⟩ =
      [⟨[1],.exact,.flow,false⟩,⟨[1],.may,.flow,true⟩,⟨[],.exact,.flow,false⟩] := by decide

theorem ancestor_may_preserves_wrapper_query :
    emit 4 ⟨[1],.may,.flow,false⟩ ⟨[],.may,fullT,true⟩ =
      [⟨[1],.exact,.flow,false⟩,⟨[1],.may,.flow,true⟩] := by decide

theorem nonempty_evidence_rejects_only_exact_empty_cell_here :
    emit 3 ⟨[1],.may,fullT,false⟩ ⟨[1],.exact,fullT,false⟩ = [] ∧
    emit 3 ⟨[1],.may,fullT,false⟩ ⟨[1],.may,fullT,true⟩ =
      [⟨[1],.exact,.flow,false⟩,⟨[1],.may,fullT,true⟩] := by decide

theorem exact_complete_first_field_is_not_widened :
    emit 3 ⟨[],.may,fullT,true⟩ ⟨[1],.exact,fullT,false⟩ =
      [⟨[1],.exact,fullT,false⟩,⟨[],.exact,.flow,false⟩] := by decide

theorem requested_run2_star_uses_two_nonstar_starts :
    emit 2 ⟨[],.star,.flow,true⟩ ⟨[1],.exact,fullT,false⟩ =
      [⟨[],.exact,.flow,false⟩,⟨[],.may,.flow,true⟩] ∧
    emit 3 ⟨[],.star,.flow,true⟩ ⟨[1],.exact,fullT,false⟩ = [] := by decide

theorem mismatched_mark_is_rejected :
    emit 3 ⟨[],.may,.full 1,true⟩ ⟨[],.may,.full 2,true⟩ = [] := by decide

theorem no_live_star_input_is_admitted :
    emit 3 rootGuide ⟨[],.star,.flow,false⟩ = [] := by decide

#print axioms family_has_no_star
#print axioms dropPrefix_sound
#print axioms first_field_may_view_covers_all_original_bindings
#print axioms deeper_demand_may_view_stays_inside_original_may
#print axioms may_family_is_demand
#print axioms emitted_initial_has_no_star
#print axioms stored_image_has_executable_raw_witness
#print axioms same_head_may_has_exact_probe_and_may
#print axioms explicit_first_field_example
#print axioms ancestor_may_preserves_wrapper_query
#print axioms nonempty_evidence_rejects_only_exact_empty_cell_here
#print axioms exact_complete_first_field_is_not_widened
#print axioms requested_run2_star_uses_two_nonstar_starts
#print axioms mismatched_mark_is_rejected
#print axioms no_live_star_input_is_admitted
end ExactMayEmission
