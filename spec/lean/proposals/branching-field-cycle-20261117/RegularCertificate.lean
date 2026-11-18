namespace RegularCertificate
set_option maxRecDepth 65536
set_option maxHeartbeats 160000000
set_option linter.unusedSimpArgs false
abbrev Word:=List Nat
abbrev Arc:=Nat × Nat × Nat
structure Nfa where
  start : Nat
  finals : List Nat
  arcs : List Arc
  deriving Repr, DecidableEq
inductive Run (arcs : List Arc) : Nat → Word → Nat → Prop
 | refl : Run arcs a [] a
 | step : (a,s,b)∈arcs → Run arcs b word c → Run arcs a (s::word) c

def Accepts (a : Nfa) (word : Word) : Prop:=∃f∈a.finals, Run a.arcs a.start word f

theorem append_runs (first : Run arcs a x b) (second : Run arcs b y c) :
    Run arcs a (x++y) c := by
  induction first with
  | refl=>exact second
  | step edge _ ih=>exact Run.step edge (ih second)

abbrev Vertex:=Nat × Nat
abbrev Graph:=List (Vertex × Vertex)
def product (a b : Nfa) : Graph:=a.arcs.flatMap fun (p,s,q)=>
  b.arcs.flatMap fun (r,t,u)=>if s=t then [((p,r),(q,u))] else []
inductive Walk (graph : Graph) : Vertex → Vertex → Prop
 | refl : Walk graph a a
 | step : (a,b)∈graph → Walk graph b c → Walk graph a c

theorem equal_symbol_edges_are_in_the_product
    (left : (p,s,q)∈a.arcs) (right : (r,s,u)∈b.arcs) :
    ((p,r),(q,u))∈product a b := by
  apply List.mem_flatMap.mpr
  refine ⟨(p,s,q),left,?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨(r,s,u),right,by simp⟩

theorem shared_word_gives_a_product_walk
    (left : Run a.arcs p word q) (right : Run b.arcs r word u) :
    Walk (product a b) (p,r) (q,u) := by
  induction left generalizing r u with
  | refl=>cases right; exact Walk.refl
  | step edge _ ih=>
    cases right with
    | step redge rest=>exact Walk.step (equal_symbol_edges_are_in_the_product edge redge) (ih rest)

def finals (a b : Nfa) : List Vertex:=a.finals.flatMap fun x=>b.finals.map fun y=>(x,y)
def next (graph : Graph) (seen : List Vertex) : List Vertex:=
  (seen++graph.flatMap (fun (a,b)=>if a∈seen then [b] else [])).eraseDups
def close (graph : Graph) : Nat → List Vertex → List Vertex
 | 0,seen=>seen
 | n+1,seen=>close graph n (next graph seen)
def scan (a b : Nfa) : List Vertex:=close (product a b) ((product a b).length+1) [(a.start,b.start)]
def closed (graph : Graph) (start : Vertex) (seen : List Vertex) : Bool:=
  decide (start∈seen) && graph.all (fun (a,b)=>decide (a∉seen ∨ b∈seen))
def certifiesEmptyWith (a b : Nfa) (seen : List Vertex) : Bool:=
  closed (product a b) (a.start,b.start) seen && (finals a b).all (fun v=>decide (v∉seen))
def certifiesEmpty (a b : Nfa) : Bool:=certifiesEmptyWith a b (scan a b)

theorem closed_seen_contains_every_reached_vertex
    (ok : closed graph start seen=true) (path : Walk graph start v) : v∈seen := by
  have halves:=Bool.and_eq_true_iff.mp ok
  have startIn:=of_decide_eq_true halves.1
  have advance : ∀a∈seen, ∀b, (a,b)∈graph → b∈seen := by
    intro a ha b edge
    have checked:=of_decide_eq_true ((List.all_eq_true.mp halves.2) (a,b) edge)
    exact checked.resolve_left (fun missing=>missing ha)
  have allPaths : ∀a b, Walk graph a b → a∈seen → b∈seen := by
    intro a b walk
    induction walk with
    | refl=>exact id
    | step edge _ ih=>intro ha; exact ih (advance _ ha _ edge)
  exact allPaths _ _ path startIn

theorem an_empty_certificate_excludes_every_shared_word
    (passed : certifiesEmptyWith a b seen=true) :
    ∀word, ¬(Accepts a word ∧ Accepts b word) := by
  intro word both
  obtain ⟨lf,hlf,wl⟩:=both.1
  obtain ⟨rf,hrf,wr⟩:=both.2
  have halves:=Bool.and_eq_true_iff.mp passed
  have path:=shared_word_gives_a_product_walk wl wr
  have reached:=closed_seen_contains_every_reached_vertex halves.1 path
  have final : (lf,rf)∈finals a b:=by
    apply List.mem_flatMap.mpr
    refine ⟨lf,hlf,?_⟩
    exact List.mem_map.mpr ⟨rf,hrf,rfl⟩
  have absent:=of_decide_eq_true ((List.all_eq_true.mp halves.2) (lf,rf) final)
  exact absent reached

theorem executable_scan_cannot_certify_a_true_route_empty
    (passed : certifiesEmpty a b=true) (left : Accepts a word) (right : Accepts b word) : False :=
  an_empty_certificate_excludes_every_shared_word passed word ⟨left,right⟩

-- The certificate checker needs a closed set, not a special BFS order.
-- This permits a linear queue implementation and arbitrary hash iteration.
theorem any_valid_closed_product_cut_is_a_sound_replacement_for_the_scan
    (passed : certifiesEmptyWith a b seen=true) (word : Word) :
    ¬(Accepts a word ∧ Accepts b word) :=
  an_empty_certificate_excludes_every_shared_word passed word

-- A finite clause grammar describes all base branches and recursive calls.
structure Clause where
  owner : Nat
  chunk : Word
  callee : Option Nat
  deriving DecidableEq, BEq, Repr
inductive Derives (grammar : List Clause) : Nat → Word → Prop
 | base : ⟨owner,chunk,none⟩∈grammar → Derives grammar owner chunk
 | call : ⟨owner,chunk,some callee⟩∈grammar → Derives grammar callee word →
     Derives grammar owner (chunk++word)

def delta (a : Nfa) (states : List Nat) (symbol : Nat) : List Nat:=
  (a.arcs.flatMap fun (p,s,q)=>if p∈states ∧ s=symbol then [q] else []).eraseDups
def runStates (a : Nfa) : List Nat → Word → List Nat
 | states,[]=>states
 | states,s::word=>runStates a (delta a states s) word

theorem delta_member_has_a_real_edge (present : q∈delta a states symbol) :
    ∃p∈states, (p,symbol,q)∈a.arcs := by
  have raw:=List.mem_eraseDups.mp present
  obtain ⟨edge,he,member⟩:=List.mem_flatMap.mp raw
  obtain ⟨p,s,r⟩:=edge
  by_cases good : p∈states ∧ s=symbol
  · simp [good] at member
    subst q
    exact ⟨p,good.1,by simpa only [good.2] using he⟩
  · simp [good] at member

theorem run_states_produces_an_executable_word_witness
    (present : q∈runStates a states word) : ∃p∈states, Run a.arcs p word q := by
  induction word generalizing states with
  | nil=>exact ⟨q,present,Run.refl⟩
  | cons symbol word ih=>
    obtain ⟨mid,hmid,tail⟩:=ih present
    obtain ⟨p,hp,edge⟩:=delta_member_has_a_real_edge hmid
    exact ⟨p,hp,Run.step edge tail⟩

def validatesClause (a : Nfa) (c : Clause) : Bool:=
  let out:=runStates a [c.owner] c.chunk
  match c.callee with
  | none=>out.any a.finals.contains
  | some target=>out.contains target

theorem validated_clause_has_its_actual_path (passed : validatesClause a c=true) :
    match c.callee with
    | none=>∃f∈a.finals, Run a.arcs c.owner c.chunk f
    | some target=>Run a.arcs c.owner c.chunk target := by
  cases c with
  | mk owner chunk callee=>
    cases callee with
    | none=>
      obtain ⟨f,hf,accept⟩:=List.any_eq_true.mp passed
      obtain ⟨p,hp,path⟩:=run_states_produces_an_executable_word_witness hf
      have same:=List.mem_singleton.mp hp
      subst p
      exact ⟨f,List.mem_of_elem_eq_true accept,path⟩
    | some target=>
      have hf : target∈runStates a [owner] chunk:=List.mem_of_elem_eq_true passed
      obtain ⟨p,hp,path⟩:=run_states_produces_an_executable_word_witness hf
      have same:=List.mem_singleton.mp hp
      subst p
      exact path

theorem every_grammar_derivation_has_a_compiled_automaton_witness
    (valid : grammar.all (validatesClause a)=true) (derivation : Derives grammar owner word) :
    ∃f∈a.finals, Run a.arcs owner word f := by
  induction derivation with
  | base member=>exact validated_clause_has_its_actual_path ((List.all_eq_true.mp valid) _ member)
  | call member _ ih=>
    have head:=validated_clause_has_its_actual_path ((List.all_eq_true.mp valid) _ member)
    obtain ⟨f,hf,rest⟩:=ih
    exact ⟨f,hf,append_runs head rest⟩

theorem all_true_ordinary_routes_survive_certified_pruning
    (validW : grammarW.all (validatesClause writer)=true)
    (validR : grammarR.all (validatesClause reader)=true)
    (pathW : Derives grammarW writer.start word)
    (pathR : Derives grammarR reader.start word)
    (passed : certifiesEmpty writer reader=true) : False := by
  exact executable_scan_cannot_certify_a_true_route_empty passed
    (every_grammar_derivation_has_a_compiled_automaton_witness validW pathW)
    (every_grammar_derivation_has_a_compiled_automaton_witness validR pathR)

-- Two states represent infinitely many choices/depths. No path enumeration.
def writer : Nfa:=⟨0,[1],[(0,1,1),(0,2,0),(0,3,0)]⟩
def reader : Nfa:=⟨0,[1],[(0,2,1),(0,2,0),(0,3,0)]⟩
def wg : List Clause:=[⟨0,[1],none⟩,⟨0,[2],some 0⟩,⟨0,[3],some 0⟩]
def rg : List Clause:=[⟨0,[2],none⟩,⟨0,[2],some 0⟩,⟨0,[3],some 0⟩]
theorem the_branching_writer_and_reader_grammars_validate :
    wg.all (validatesClause writer)=true ∧ rg.all (validatesClause reader)=true := by decide
theorem the_infinite_branching_languages_have_an_empty_product :
    certifiesEmpty writer reader=true := by decide
theorem no_depth_and_no_branch_can_reach_the_exact_observer (word : Word) :
    ¬(Derives wg 0 word ∧ Derives rg 0 word) := by
  intro both
  exact all_true_ordinary_routes_survive_certified_pruning
    the_branching_writer_and_reader_grammars_validate.1
    the_branching_writer_and_reader_grammars_validate.2 both.1 both.2
    the_infinite_branching_languages_have_an_empty_product
end RegularCertificate

namespace RegularCertificate
-- An identical last symbol is not enough. Parity can be the separating
-- invariant even when every long path has the same finite suffix.
def parityWriter : Nfa:=⟨0,[2],[(0,2,1),(1,2,0),(0,1,2)]⟩
def parityReader : Nfa:=⟨0,[3],[(0,2,1),(1,2,0),(0,2,2),(2,1,3)]⟩
def pwg : List Clause:=[⟨0,[1],none⟩,⟨0,[2,2],some 0⟩]
def prg : List Clause:=[⟨0,[2,1],none⟩,⟨0,[2,2],some 0⟩]
theorem parity_grammars_have_complete_finite_word_paths :
    pwg.all (validatesClause parityWriter)=true ∧ prg.all (validatesClause parityReader)=true := by decide
theorem arbitrarily_long_equal_suffixes_do_not_defeat_the_parity_certificate :
    certifiesEmpty parityWriter parityReader=true := by decide

def chunkWriter : Nfa:=⟨0,[2],[(0,1,1),(1,3,2),(0,2,0),(0,3,0)]⟩
def chunkReader : Nfa:=⟨0,[2],[(0,2,1),(1,3,2),(0,2,0),(0,3,0)]⟩
theorem complete_terminal_chunks_can_separate_equal_last_fields :
    certifiesEmpty chunkWriter chunkReader=true := by decide

def overlapReader : Nfa:=⟨0,[1],[(0,1,1),(0,2,0),(0,3,0)]⟩
theorem a_real_shared_word_prevents_certification : certifiesEmpty writer overlapReader=false := by decide
end RegularCertificate
