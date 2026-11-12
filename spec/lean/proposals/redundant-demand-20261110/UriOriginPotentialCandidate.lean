import Std
namespace UriOriginPotentialCandidate
/- Candidate component. No native adapter or retirement theorem is asserted. -/
abbrev Word := List Nat
structure Relation where
  input : Word
  output : Word
  deriving DecidableEq, Repr
structure Copy where
  source : Word
  target : Word
  deriving DecidableEq, Repr
def depth (r : Relation) : Int := (r.output.length : Int) - (r.input.length : Int)
def weight (c : Copy) : Int := (c.target.length : Int) - (c.source.length : Int)
inductive Step (c : Copy) : Relation → Relation → Prop
  | known (i rest : Word) : Step c ⟨i, c.source ++ rest⟩ ⟨i, c.target ++ rest⟩
  | input (o rest i : Word) (source : c.source = o ++ rest) : Step c ⟨i,o⟩ ⟨i ++ rest,c.target⟩
theorem step_depth (c : Copy) (r s : Relation) (step : Step c r s) :
    depth s = depth r + weight c := by
  cases step with
  | known i rest => simp [depth, weight]; omega
  | input o rest i source => simp [depth, weight, source]; omega
theorem step_no_literal_uri (uri : Nat) (c : Copy) (r s : Relation)
    (step : Step c r s) (old : uri ∉ r.output) (writer : uri ∉ c.target) : uri ∉ s.output := by
  cases step with
  | known i rest => simp only [List.mem_append, not_or] at old ⊢; exact ⟨writer,old.2⟩
  | input _ _ _ _ => exact writer
structure Arc where
  sourceVertex : Nat
  dest : Nat
  copy : Copy
  deriving DecidableEq, Repr
def checkArc (uri : Nat) (selected : List Nat) (potential : Nat → Int) (arc : Arc) : Bool :=
  if selected.contains arc.sourceVertex then
    selected.contains arc.dest && decide (potential arc.dest ≤ potential arc.sourceVertex + weight arc.copy) &&
      !arc.copy.target.contains uri else true
theorem checked_arc (uri : Nat) (selected : List Nat) (potential : Nat → Int)
    (arcs : List Arc) (checked : arcs.all (checkArc uri selected potential) = true)
    (arc : Arc) (member : arc ∈ arcs) (active : arc.sourceVertex ∈ selected) :
    arc.dest ∈ selected ∧ potential arc.dest ≤ potential arc.sourceVertex + weight arc.copy ∧ uri ∉ arc.copy.target := by
  have h := (List.all_eq_true.mp checked) arc member
  simpa [checkArc, active, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h
inductive Reach (arcs : List Arc) (start : Nat) : Nat → Relation → Prop
  | entry : Reach arcs start start ⟨[],[]⟩
  | transfer (vertex : Nat) (r s : Relation) (arc : Arc) (member : arc ∈ arcs)
      (sourceVertex : arc.sourceVertex = vertex) (before : Reach arcs start vertex r) (copy : Step arc.copy r s) : Reach arcs start arc.dest s
theorem inductive_origin_invariant (uri : Nat) (selected : List Nat) (potential : Nat → Int)
    (arcs : List Arc) (checked : arcs.all (checkArc uri selected potential) = true)
    (start : Nat) (startActive : start ∈ selected) (startPotential : potential start ≤ 0)
    (vertex : Nat) (r : Relation) (reachable : Reach arcs start vertex r) :
    vertex ∈ selected ∧ potential vertex ≤ depth r ∧ uri ∉ r.output := by
  induction reachable with
  | entry => exact ⟨startActive,by simpa [depth] using startPotential,by simp⟩
  | transfer vertex old new arc member sourceVertex before copy ih =>
    have active : arc.sourceVertex ∈ selected := by simpa only [sourceVertex] using ih.1
    rcases checked_arc uri selected potential arcs checked arc member active with ⟨dest,lower,writer⟩
    have oldLower : potential arc.sourceVertex ≤ depth old := by simpa only [sourceVertex] using ih.2.1
    refine ⟨dest,?_,step_no_literal_uri uri arc.copy old new copy ih.2.2 writer⟩
    rw [step_depth arc.copy old new copy]
    omega
theorem uri_output_has_no_inserted_prefix (uri : Nat) (r : Relation) (suffix tail : Word)
    (noLiteral : uri ∉ r.output) (out : r.output ++ suffix = uri :: tail) : r.output = [] := by
  cases h : r.output with
  | nil => rfl
  | cons a rest =>
    have equal : a = uri := (List.cons.inj (by simpa only [h, List.cons_append] using out)).1
    have bad : uri ∈ r.output := by simp [h, equal]
    exact False.elim (noLiteral bad)
theorem nonnegative_root_has_no_read_debt (r : Relation) (nonnegative : 0 ≤ depth r)
    (root : r.output = []) : r.input = [] := by
  have lengthZero : r.input.length = 0 := by simp only [depth, root, List.length_nil, Int.natCast_zero] at nonnegative; omega
  exact List.length_eq_zero_iff.mp lengthZero
/- A retained NORMAL root-to-root relation replays this same concrete word.
   MAY candidates and native source/cleaner/callee correspondence stay outside
   this component until their actual guards are proved. -/
theorem retained_root_replays_every_uri_transfer (uri : Nat) (selected : List Nat)
    (potential : Nat → Int) (arcs : List Arc)
    (checked : arcs.all (checkArc uri selected potential) = true)
    (start : Nat) (startActive : start ∈ selected) (startPotential : potential start ≤ 0)
    (vertex : Nat) (r : Relation) (reachable : Reach arcs start vertex r)
    (exitPotential : 0 ≤ potential vertex) (suffix tail : Word)
    (out : r.output ++ suffix = uri :: tail) : r.input ++ suffix = uri :: tail := by
  rcases inductive_origin_invariant uri selected potential arcs checked start startActive startPotential vertex r reachable with ⟨_,lower,noLiteral⟩
  have root := uri_output_has_no_inserted_prefix uri r suffix tail noLiteral out
  have nonnegative : 0 ≤ depth r := Int.le_trans exitPotential lower
  have inputRoot := nonnegative_root_has_no_read_debt r nonnegative root
  simpa only [root,inputRoot,List.nil_append] using out
def readCandidate : Relation := ⟨[7],[]⟩
theorem unmatched_reader_negative_control :
    20 ∉ readCandidate.output ∧ readCandidate.output ++ [20] = [20] ∧
      readCandidate.input ++ [20] ≠ [20] ∧ depth readCandidate < 0 := by decide
def literalAlias : Copy := ⟨[],[20,24]⟩
theorem false_literal_writer_is_not_automatically_root_replay :
    Step literalAlias ⟨[],[]⟩ ⟨[],[20,24]⟩ ∧ ([] : Word) ≠ [20,24] := by
  exact ⟨Step.known [] [],by decide⟩
end UriOriginPotentialCandidate
#print axioms UriOriginPotentialCandidate.step_depth
#print axioms UriOriginPotentialCandidate.step_no_literal_uri
#print axioms UriOriginPotentialCandidate.checked_arc
#print axioms UriOriginPotentialCandidate.inductive_origin_invariant
#print axioms UriOriginPotentialCandidate.uri_output_has_no_inserted_prefix
#print axioms UriOriginPotentialCandidate.nonnegative_root_has_no_read_debt
#print axioms UriOriginPotentialCandidate.retained_root_replays_every_uri_transfer
#print axioms UriOriginPotentialCandidate.unmatched_reader_negative_control
#print axioms UriOriginPotentialCandidate.false_literal_writer_is_not_automatically_root_replay
