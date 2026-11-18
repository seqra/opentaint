import RegularCertificate

namespace PairedContext
open RegularCertificate
local instance : ReflBEq Nat where rfl := by intro n; exact decide_eq_true rfl
local instance : LawfulBEq Nat where
  rfl := by intro n; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

/-- A nonterminal contributes the fields before and after one nested result. -/
inductive Rule where
  | base (owner : Nat) (word : Word)
  | nested (owner : Nat) (lead : Word) (child : Nat) (suffix : Word)
  deriving Repr, DecidableEq

inductive Derives (rules : List Rule) : Nat → Word → Prop
  | base : Rule.base owner word ∈ rules → Derives rules owner word
  | nested : Rule.nested owner lead child suffix ∈ rules →
      Derives rules child word → Derives rules owner (lead ++ word ++ suffix)

abbrev Cell := Nat × Nat × Nat

def states (reader : Nfa) : List Nat :=
  (reader.start :: reader.finals ++ reader.arcs.flatMap (fun (p,_,q) => [p,q])).eraseDups

def move (reader : Nfa) (start : Nat) (word : Word) := runStates reader [start] word

def consequences (reader : Nfa) (seen : List Cell) : Rule → List Cell
  | .base owner word => (states reader).flatMap fun p =>
      (move reader p word).map fun q => (owner,p,q)
  | .nested owner lead child suffix => (states reader).flatMap fun p =>
      (move reader p lead).flatMap fun m =>
        seen.flatMap fun (callee,start,stop) =>
          if callee == child && start == m then (move reader stop suffix).map fun q => (owner,p,q) else []

def closureStep (rules : List Rule) (reader : Nfa) (seen : List Cell) : List Cell :=
  (seen ++ rules.flatMap (consequences reader seen)).eraseDups

def closed (rules : List Rule) (reader : Nfa) (seen : List Cell) : Bool :=
  rules.all fun r => (consequences reader seen r).all seen.contains

def eligible (reader : Nfa) (suffix : Word) (state : Nat) : Bool :=
  (move reader state suffix).any reader.finals.contains

def certifies (rules : List Rule) (reader : Nfa) (start : Nat) (suffix : Word)
    (seen : List Cell) : Bool :=
  closed rules reader seen &&
    seen.all (fun (owner,p,q) => !(owner == start && p == reader.start && eligible reader suffix q))

theorem run_endpoints_in_states (run : Run a.arcs p word q) (start : p ∈ states a) :
    q ∈ states a := by
  induction run with
  | refl => exact start
  | @step x symbol y z tail edge _ ih =>
    apply ih
    apply List.mem_eraseDups.mpr
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    exact ⟨(x,symbol,y),edge,by simp⟩

theorem run_target_in_move {a : Nfa} (run : Run a.arcs p word q) : q ∈ move a p word := by
  have go : ∀ (w : Word) (p q : Nat) (ss : List Nat), p ∈ ss →
      Run a.arcs p w q → q ∈ runStates a ss w := by
    intro w
    induction w with
    | nil =>
      intro p q ss hp path
      cases path
      exact hp
    | cons f ws ih =>
      intro p q ss hp path
      cases path with
      | @step _ _ y _ _ edge rest =>
        apply ih y q (delta a ss f) _ rest
        apply List.mem_eraseDups.mpr
        apply List.mem_flatMap.mpr
        exact ⟨(p,f,y),edge,by simp [hp]⟩
  exact go word p q [p] (by simp) run

theorem split_run (run : Run arcs p (left ++ right) q) :
    ∃ m, Run arcs p left m ∧ Run arcs m right q := by
  induction left generalizing p with
  | nil => exact ⟨p,Run.refl,run⟩
  | cons f rest ih =>
    cases run with
    | step edge run =>
      obtain ⟨m,first,last⟩ := ih run
      exact ⟨m,Run.step edge first,last⟩

theorem all_derived_transfers_belong_to_closed_cells {reader : Nfa}
    (complete : closed rules reader cells = true)
    (tree : Derives rules owner word)
    (inGraph : p ∈ states reader) (path : Run reader.arcs p word q) :
    (owner,p,q) ∈ cells := by
  have unlock : ∀ r ∈ rules, ∀ cell ∈ consequences reader cells r, cell ∈ cells := by
    intro r hr cell hc
    exact List.mem_of_elem_eq_true (List.all_eq_true.mp (List.all_eq_true.mp complete r hr) cell hc)
  induction tree generalizing p q with
  | base rule =>
    apply unlock _ rule
    apply List.mem_flatMap.mpr
    exact ⟨p,inGraph,List.mem_map.mpr ⟨q,run_target_in_move path,rfl⟩⟩
  | @nested owner lead child suffix word rule _ ih =>
    obtain ⟨n,firstTwo,after⟩ := split_run path
    obtain ⟨m,before,inside⟩ := split_run firstTwo
    have central := ih (run_endpoints_in_states before inGraph) inside
    apply unlock _ rule
    apply List.mem_flatMap.mpr
    refine ⟨p,inGraph,List.mem_flatMap.mpr ⟨m,run_target_in_move before,?_⟩⟩
    apply List.mem_flatMap.mpr
    exact ⟨(child,m,n),central,by simpa using run_target_in_move after⟩

theorem a_checked_certificate_cannot_remove_any_shared_exact_path {reader : Nfa}
    (verified : certifies rules reader root sourceSuffix cells = true)
    (writerPath : Derives rules root w) (actual : Accepts reader (w ++ sourceSuffix)) : False := by
  obtain ⟨f,hf,route⟩ := actual
  obtain ⟨q,head,tail⟩ := split_run route
  have parts := Bool.and_eq_true_iff.mp verified
  have reachable := all_derived_transfers_belong_to_closed_cells parts.1 writerPath (by simp [states]) head
  have noticed : eligible reader sourceSuffix q = true :=
    List.any_eq_true.mpr ⟨f,run_target_in_move tail,List.elem_eq_true_of_mem hf⟩
  have absent := List.all_eq_true.mp parts.2 _ reachable
  simp [noticed] at absent


def saturate (rules : List Rule) (reader : Nfa) : Nat → List Cell → List Cell
  | 0, cells => cells
  | fuel+1, cells =>
    let next := closureStep rules reader cells
    if next == cells then cells else saturate rules reader fuel next

def check (rules : List Rule) (owners : Nat) (other : Nfa)
    (suffix : Word := []) : Bool :=
  let stateCount := (states other).length
  let cells := saturate rules other (owners * stateCount * stateCount + 1) []
  certifies rules other 0 suffix cells

def writer : Nfa := ⟨0, [1], [(0,1,1),(0,2,0)]⟩
def reader : List Rule := [.base 0 [2], .nested 0 [2] 0 [], .nested 0 [3] 0 [3]]
def validReader : List Rule := reader ++ [.base 0 [1]]

theorem the_nested_reader_has_no_shared_word : check reader 1 writer = true := by decide
theorem admitting_the_writer_base_prevents_retirement :
    check validReader 1 writer = false := by decide

-- The source suffix is outside the entire recursion. Appending it to each
-- grammar base would insert h between g and f in this one-level route.
def suffixGrammar : List Rule := [.base 0 [], .nested 0 [2] 0 [1]]
def suffixObserver : Nfa := ⟨0,[3],[(0,2,1),(1,1,2),(2,3,3)]⟩
theorem a_suffix_after_a_recursive_return_is_never_appended_at_the_base :
    check suffixGrammar 1 suffixObserver [3] = false ∧
    check [.base 0 [3], .nested 0 [2] 0 [1]] 1 suffixObserver = true := by decide

def layeredWriter : List Rule := [.base 0 [1], .nested 0 [2] 0 [1]]
def regularReader : Nfa := ⟨0,[1],[(0,2,0),(0,2,1)]⟩
theorem the_finite_check_works_on_a_nested_writer_as_well :
    check layeredWriter 1 regularReader = true := by decide

-- Positive certificate proofs remain independent of saturation fuel.
theorem the_search_budget_cannot_change_certificate_safety
    (proof : check rules count other suffix = true)
    (word : Derives rules 0 path) (accepts : Accepts other (path ++ suffix)) : False :=
  a_checked_certificate_cannot_remove_any_shared_exact_path proof word accepts

end PairedContext
