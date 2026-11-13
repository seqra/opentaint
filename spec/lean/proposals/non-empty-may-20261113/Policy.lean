import NonEmptyMay

namespace NonEmptyPolicy

abbrev Path := List Nat
inductive Tail where | exact | star | may | ne | must
  deriving DecidableEq, BEq, Repr
structure Ap where
  base : Nat := 0
  path : Path := []
  tail : Tail
  mark : Option Nat := none
  e : List Nat := []
  mx : List Nat := []
  deriving DecidableEq, BEq, Repr
structure Offered where
  ap : Ap
  demand : Bool := false
  deriving DecidableEq, BEq, Repr
structure Seed where
  ap : Ap
  demand : Bool := false
  deriving DecidableEq, BEq, Repr

def dropHead : Path → Path → Option Path
  | [], rest => some rest
  | _ :: _, [] => none
  | f :: fs, a :: rest => if f = a then dropHead fs rest else none

def marksOK (d a : Ap) : Bool :=
  match d.mark,a.mark with
  | some t,some u => t == u
  | some _,none => false
  | none,some t => !d.mx.contains t
  | none,none => d.mx.all a.mx.contains

def admits (tail : Tail) (e : List Nat) : Path → Bool
  | [] => tail != .ne
  | f :: _ => tail != .exact &&
      ((tail != .star && tail != .must) || !e.contains f)

def selector (d : Ap) : Ap :=
  if d.mark.isNone && d.tail == .star then {d with e := []} else d

def seed (d : Ap) (a : Offered) (path : Path) (tail : Tail)
    (e : List Nat := []) : Seed :=
  ⟨{d with path := path,tail := tail,e := e,mx := []},
   match d.mark with
   | none => false
   | some _ => tail == .star || a.demand || a.ap.tail == .may || a.ap.tail == .ne⟩

def probe (d : Ap) : Seed :=
  ⟨{d with tail := .exact,mark := none,e := [],mx := []},false⟩

def atHead (d : Ap) (a : Offered) : List Seed :=
  match d.tail,a.ap.tail with
  | .may,.exact => [seed d a d.path .exact]
  | .may,.may => [seed d a d.path .exact,seed d a d.path .star]
  | .may,.star | .may,.ne => [seed d a d.path .star]
  | .may,.must => [seed d a d.path .must a.ap.e]
  | .ne,.exact => []
  | .ne,.must => [seed d a d.path .must a.ap.e]
  | .ne,_ => [seed d a d.path .star]
  | .star,.exact | .star,.may | .star,.must
  | .exact,.exact | .exact,.may | .exact,.must => [seed d a d.path .exact]
  | _,_ => []

def primary (run : Nat) (d : Ap) (a : Offered) : List Seed :=
  if d.path == a.ap.path then atHead d a
  else match dropHead d.path a.ap.path with
  | some (f :: rest) =>
      if !admits d.tail d.e (f :: rest) then []
      else if d.tail == .star then
        if run == 2 then [seed d a d.path .star d.e] else []
      else if d.tail == .may || d.tail == .ne then
        let r := d.path ++ [f]
        if !rest.isEmpty then [seed d a r .star]
        else match a.ap.tail with
          | .exact => [seed d a r .exact]
          | .may => [seed d a r .exact,seed d a r .star]
          | _ => [seed d a r .star]
      else []
  | _ => match dropHead a.ap.path d.path with
      | some (f :: rest) =>
        if !admits a.ap.tail a.ap.e (f :: rest) ||
            a.ap.tail == .star || a.ap.tail == .exact then []
        else
          let rebased : Ap := {a.ap with path := d.path,tail := (if a.ap.tail == .must then .must else .may),e := []}
          let narrowed : Offered := {a with ap := rebased}
          atHead d narrowed
      | _ => []

def completeFamily (run : Nat) (d : Ap) (a : Offered) : List Seed :=
  let raw := primary run d a
  if raw.isEmpty then [] else
  let companions := raw.filterMap fun q =>
    if q.ap.tail == .star && q.ap.mark.isSome then
      some {q with ap := {q.ap with mark := none,mx := []},demand := false}
    else none
  let extra := match dropHead d.path a.ap.path with
    | some (_ :: _) => if d.tail == .may then [probe d] else []
    | _ => []
  raw ++ companions ++ extra

abbrev legalSeed (limit : Nat) (d : Ap) (s : Seed) : Prop :=
  s.ap.path.length ≤ limit ∧ s.ap.path.length ≤ d.path.length + 1 ∧
    (s.ap.tail = .exact ∨ s.ap.tail = .star ∨ s.ap.tail = .must)

def emitBase (run limit : Nat) (backward : Bool) (inputDemand : Ap)
    (a : Offered) : List Seed :=
  let d := selector inputDemand
  if limit == 0 || !marksOK d a.ap || d.base != a.ap.base ||
      d.path.length > limit || a.ap.path.length > limit || d.tail == .must ||
      (d.tail == .exact && d.mark.isNone) ||
      (backward && a.ap.tail == .must) then []
  else (completeFamily run d a).filter fun s =>
    decide (legalSeed limit d s) && !(backward && s.ap.tail == .must)

theorem base_emitted_legal (run limit : Nat) (backward : Bool) (d : Ap)
    (a : Offered) (s : Seed) (h : s ∈ emitBase run limit backward d a) :
    legalSeed limit (selector d) s := by
  unfold emitBase at h
  dsimp only at h
  split at h
  · cases h
  · have checked := (List.mem_filter.mp h).2
    have yes : decide (legalSeed limit (selector d) s) = true := by
      cases hl : decide (legalSeed limit (selector d) s) <;> simp_all
    exact of_decide_eq_true yes

-- An NE selector is the positive branch of the MAY family. This also
-- removes MAY's conditional exact prefix probe at the same head, while
-- retaining exact starts at a known proper descendant and the MUST lane.
def emit (run limit : Nat) (backward : Bool) (d : Ap) (a : Offered) : List Seed :=
  if d.tail = .ne then
    (emitBase run limit backward {d with tail := .may} a).filter fun s =>
      decide (s.ap.tail ≠ .exact ∨ s.ap.path ≠ d.path)
  else emitBase run limit backward d a

theorem selector_path (d : Ap) : (selector d).path = d.path := by
  unfold selector; split <;> rfl

theorem emitted_legal (run limit : Nat) (backward : Bool) (d : Ap)
    (a : Offered) (s : Seed) (h : s ∈ emit run limit backward d a) :
    legalSeed limit (selector d) s := by
  unfold emit at h
  split at h
  · have core := base_emitted_legal run limit backward {d with tail := .may} a s
      (List.mem_filter.mp h).1
    simpa only [legalSeed,selector_path] using core
  · exact base_emitted_legal run limit backward d a s h

theorem emitted_no_may_or_ne_initial (run limit : Nat) (backward : Bool)
    (d : Ap) (a : Offered) (s : Seed) (h : s ∈ emit run limit backward d a) :
    s.ap.tail ≠ .may ∧ s.ap.tail ≠ .ne := by
  rcases (emitted_legal run limit backward d a s h).2.2 with he | hs | hm
  · rw [he]; decide
  · rw [hs]; decide
  · rw [hm]; decide

theorem no_same_head_empty_initial_under_ne (run limit : Nat) (backward : Bool)
    (d : Ap) (a : Offered) (s : Seed) (h : s ∈ emit run limit backward d a)
    (ne : d.tail = .ne) (head : s.ap.path = d.path) :
    s.ap.tail ≠ .exact := by
  unfold emit at h
  rw [if_pos ne] at h
  have checked := of_decide_eq_true (List.mem_filter.mp h).2
  rcases checked with tail | notHead
  · exact tail
  · exact False.elim (notHead head)

theorem every_ne_query_is_a_may_query (run limit : Nat) (backward : Bool)
    (d : Ap) (a : Offered) (s : Seed)
    (h : s ∈ emit run limit backward {d with tail := .ne} a) :
    s ∈ emit run limit backward {d with tail := .may} a := by
  change s ∈ List.filter _ (emitBase run limit backward {d with tail := .may} a) at h
  exact (List.mem_filter.mp h).1

def flow (tail : Tail) (path : Path := []) : Ap := ⟨0,path,tail,none,[],[]⟩
def full (tail : Tail) (path : Path := []) : Ap := ⟨0,path,tail,some 7,[],[]⟩

theorem selected_two_concrete_starts_and_existing_flow_companion :
    emit 3 2 false (full .may) ⟨full .may,true⟩ =
      [⟨full .exact,true⟩,⟨full .star,true⟩,⟨flow .star,false⟩] := by decide

theorem ne_demand_cannot_start_same_head_exact :
    emit 3 2 false (flow .ne) ⟨flow .may,true⟩ = [⟨flow .star,false⟩] := by decide

theorem must_query_is_retained_for_both_demands :
    emit 3 2 false (flow .may) ⟨full .must,false⟩ = [⟨flow .must,false⟩] ∧
    emit 3 2 false (flow .ne) ⟨full .must,false⟩ = [⟨flow .must,false⟩] := by decide

theorem first_new_field_refines_without_inventing_more_fields :
    emit 3 3 false (full .ne) ⟨full .exact [1,2,3],false⟩ =
      [⟨full .star [1],true⟩,⟨flow .star [1],false⟩] := by decide

theorem may_residual_at_first_field_splits_again :
    emit 3 2 false (full .may) ⟨full .may [1],true⟩ =
      [⟨full .exact [1],true⟩,⟨full .star [1],true⟩,
       ⟨flow .star [1],false⟩,⟨flow .exact,false⟩] := by decide

theorem conditional_prefix_probe_is_retained_only_for_may :
    emit 3 2 false (full .may) ⟨full .exact [1],false⟩ =
      [⟨full .exact [1],false⟩,⟨flow .exact,false⟩] ∧
    emit 3 2 false (full .ne) ⟨full .exact [1],false⟩ =
      [⟨full .exact [1],false⟩] := by decide

theorem ancestor_star_still_rejects :
    emit 3 2 false (full .exact [1]) ⟨full .star,true⟩ = [] := by decide

theorem ancestor_ne_can_become_empty_after_descent :
    emit 3 2 false (full .exact [1]) ⟨full .ne,true⟩ =
      [⟨full .exact [1],true⟩] := by decide

theorem run2_requested_star_exception_is_not_extended :
    emit 2 2 true (flow .star) ⟨full .exact [1],false⟩ = [⟨flow .star,false⟩] ∧
    emit 3 2 false (flow .star) ⟨full .exact [1],false⟩ = [] := by decide

-- A finite list is an explicit executable actual domain for this image
-- calculation. The theorem does not assume sampled offers are complete.
def rawImage (run limit : Nat) (backward : Bool) (d : Ap)
    (actualDomain : List Offered) : List Ap :=
  actualDomain.flatMap fun a => (emit run limit backward d a).map Seed.ap

theorem raw_image_has_constructive_offer (run limit : Nat) (backward : Bool)
    (d : Ap) (domain : List Offered) (key : Ap)
    (h : key ∈ rawImage run limit backward d domain) :
    ∃ a ∈ domain, ∃ command ∈ emit run limit backward d a, command.ap = key := by
  rcases List.mem_flatMap.mp h with ⟨a,member,inside⟩
  rcases List.mem_map.mp inside with ⟨command,emitted,same⟩
  exact ⟨a,member,command,emitted,same⟩

theorem ne_raw_image_excludes_same_head_exact_for_every_domain
    (run limit : Nat) (backward : Bool) (d : Ap) (domain : List Offered)
    (key : Ap) (ne : d.tail = .ne) (head : key.path = d.path)
    (point : key.tail = .exact) : key ∉ rawImage run limit backward d domain := by
  intro member
  rcases raw_image_has_constructive_offer run limit backward d domain key member with
    ⟨a,_,command,emitted,same⟩
  have commandHead : command.ap.path = d.path := by rw [same]; exact head
  have nonpoint := no_same_head_empty_initial_under_ne run limit backward d a command
    emitted ne commandHead
  apply nonpoint
  rw [same]
  exact point

def normalAp (p : Ap) : Ap := if p.tail == .exact then {p with tail := .star} else p
def publicImage (run limit : Nat) (backward : Bool) (d : Ap)
    (domain : List Offered) : List Ap :=
  (rawImage run limit backward d domain).map normalAp

theorem normalization_erases_the_branch_distinction :
    normalAp (flow .exact) = normalAp (flow .star) := by decide

theorem normalized_alternative_is_not_a_raw_entry_witness :
    flow .exact ∉ rawImage 3 2 false (flow .ne) [⟨flow .may,true⟩] ∧
    flow .star ∈ publicImage 3 2 false (flow .ne) [⟨flow .may,true⟩] := by
  simp only [publicImage,rawImage,List.flatMap_cons,List.flatMap_nil,
    ne_demand_cannot_start_same_head_exact,List.map_cons,List.map_nil,List.append_nil]
  simp [normalAp,flow]
  rfl

#print axioms emitted_legal
#print axioms base_emitted_legal
#print axioms selector_path
#print axioms emitted_no_may_or_ne_initial
#print axioms no_same_head_empty_initial_under_ne
#print axioms every_ne_query_is_a_may_query
#print axioms selected_two_concrete_starts_and_existing_flow_companion
#print axioms ne_demand_cannot_start_same_head_exact
#print axioms must_query_is_retained_for_both_demands
#print axioms first_new_field_refines_without_inventing_more_fields
#print axioms may_residual_at_first_field_splits_again
#print axioms conditional_prefix_probe_is_retained_only_for_may
#print axioms ancestor_star_still_rejects
#print axioms ancestor_ne_can_become_empty_after_descent
#print axioms run2_requested_star_exception_is_not_extended
#print axioms raw_image_has_constructive_offer
#print axioms ne_raw_image_excludes_same_head_exact_for_every_domain
#print axioms normalization_erases_the_branch_distinction
#print axioms normalized_alternative_is_not_a_raw_entry_witness

end NonEmptyPolicy
