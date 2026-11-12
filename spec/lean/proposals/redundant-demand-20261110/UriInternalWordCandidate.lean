import Std
namespace BalancedPrefixOriginCandidate
/- Structural component for a finite PDS certificate. Eps/Push/Pop/Input
   are source-graph edges. B/R must be instantiated from checked finite
   postfixed tables; no native adapter or retirement conclusion is assumed. -/
abbrev Binary := Nat → Nat → Prop
abbrev Labeled := Nat → Nat → Nat → Prop
structure BalanceLaws (Eps : Binary) (Push Pop : Labeled) (B : Binary) : Prop where
  refl : ∀ q, B q q
  epsilon : ∀ p q, Eps p q → B p q
  trans : ∀ p q r, B p q → B q r → B p r
  wrap : ∀ p f a b q, Push p f a → B a b → Pop b f q → B p q
structure EmptyLaws (Input : Labeled) (B : Binary) (R : Nat → Bool → Prop) (source : Nat) : Prop where
  entry : R source false
  balanced : ∀ p q bad, R p bad → B p q → R q bad
  input : ∀ p f q bad, R p bad → Input p f q → R q true

/- A derivation records pending PUSH frames and a completed balanced segment.
   Thus POP cannot cross a mismatched field or unmatched method-helper return. -/
inductive State (Push : Labeled) (B : Binary) (R : Nat → Bool → Prop) : Nat → List Nat → Bool → Prop
  | base (seed q : Nat) (bad : Bool) (empty : R seed bad) (segment : B seed q) : State Push B R q [] bad
  | frame (p f a q : Nat) (stack : List Nat) (bad : Bool)
      (outer : State Push B R p stack bad) (push : Push p f a) (segment : B a q) :
      State Push B R q (f :: stack) bad

theorem advance {Eps : Binary} {Push Pop : Labeled} {B : Binary} {R : Nat → Bool → Prop}
    (laws : BalanceLaws Eps Push Pop B) (p q : Nat) (stack : List Nat) (bad : Bool)
    (state : State Push B R p stack bad) (segment : B p q) : State Push B R q stack bad := by
  cases state with
  | base seed p bad empty inner => exact State.base seed q bad empty (laws.trans seed p q inner segment)
  | frame before f a p rest bad outer push inner =>
    exact State.frame before f a q rest bad outer push (laws.trans a p q inner segment)

theorem pop_known {Eps : Binary} {Push Pop : Labeled} {B : Binary} {R : Nat → Bool → Prop}
    (laws : BalanceLaws Eps Push Pop B) (p f q : Nat) (rest : List Nat) (bad : Bool)
    (state : State Push B R p (f :: rest) bad) (pop : Pop p f q) : State Push B R q rest bad := by
  cases state with
  | frame before f a p rest bad outer push inner =>
    exact advance laws before q rest bad outer (laws.wrap before f a p q push inner pop)

theorem pop_input {Eps : Binary} {Push Pop Input : Labeled} {B : Binary} {R : Nat → Bool → Prop}
    (laws : BalanceLaws Eps Push Pop B) (emptyLaws : EmptyLaws Input B R source)
    (p f q : Nat) (bad : Bool) (state : State Push B R p [] bad) (pop : Input p f q) :
    State Push B R q [] true := by
  cases state with
  | base seed p bad before segment =>
    exact State.base q q true (emptyLaws.input p f q bad (emptyLaws.balanced seed p bad before segment) pop) (laws.refl q)

inductive Move (Eps : Binary) (Push Pop Input : Labeled) :
    (Nat × List Nat × Bool) → (Nat × List Nat × Bool) → Prop
  | epsilon (p q : Nat) (stack : List Nat) (bad : Bool) (edge : Eps p q) :
      Move Eps Push Pop Input (p,stack,bad) (q,stack,bad)
  | push (p f q : Nat) (stack : List Nat) (bad : Bool) (edge : Push p f q) :
      Move Eps Push Pop Input (p,stack,bad) (q,f::stack,bad)
  | pop (p f q : Nat) (stack : List Nat) (bad : Bool) (edge : Pop p f q) :
      Move Eps Push Pop Input (p,f::stack,bad) (q,stack,bad)
  | input (p f q : Nat) (bad : Bool) (edge : Input p f q) :
      Move Eps Push Pop Input (p,[],bad) (q,[],true)

theorem move_preserves {Eps : Binary} {Push Pop Input : Labeled} {B : Binary} {R : Nat → Bool → Prop}
    (laws : BalanceLaws Eps Push Pop B) (emptyLaws : EmptyLaws Input B R source)
    (p q : Nat) (before after : List Nat) (old new : Bool)
    (state : State Push B R p before old) (step : Move Eps Push Pop Input (p,before,old) (q,after,new)) :
    State Push B R q after new := by
  cases step with
  | epsilon _ _ _ _ edge => exact advance laws _ _ _ _ state (laws.epsilon _ _ edge)
  | push _ _ _ _ _ edge => exact State.frame _ _ _ _ _ _ state edge (laws.refl _)
  | pop _ _ _ _ _ edge => exact pop_known laws _ _ _ _ _ state edge
  | input _ _ _ _ edge => exact pop_input laws emptyLaws _ _ _ _ state edge

inductive Trace (Eps : Binary) (Push Pop Input : Labeled) (source : Nat) : Nat → List Nat → Bool → Prop
  | start : Trace Eps Push Pop Input source source [] false
  | next (p q : Nat) (before after : List Nat) (old new : Bool)
      (earlier : Trace Eps Push Pop Input source p before old)
      (step : Move Eps Push Pop Input (p,before,old) (q,after,new)) : Trace Eps Push Pop Input source q after new

theorem trace_has_state {Eps : Binary} {Push Pop Input : Labeled} {B : Binary} {R : Nat → Bool → Prop}
    (laws : BalanceLaws Eps Push Pop B) (emptyLaws : EmptyLaws Input B R source)
    (q : Nat) (stack : List Nat) (bad : Bool) (run : Trace Eps Push Pop Input source q stack bad) :
    State Push B R q stack bad := by
  induction run with
  | start => exact State.base source source false emptyLaws.entry (laws.refl source)
  | next p q before after old new earlier step ih => exact move_preserves laws emptyLaws p q before after old new ih step

theorem empty_trace_is_in_table {Eps : Binary} {Push Pop Input : Labeled} {B : Binary} {R : Nat → Bool → Prop}
    (laws : BalanceLaws Eps Push Pop B) (emptyLaws : EmptyLaws Input B R source)
    (q : Nat) (bad : Bool) (run : Trace Eps Push Pop Input source q [] bad) : R q bad := by
  have state := trace_has_state laws emptyLaws q [] bad run
  cases state with
  | base seed q bad before segment => exact emptyLaws.balanced seed q bad before segment

theorem no_input_pop_at_goal {Eps : Binary} {Push Pop Input : Labeled} {B : Binary} {R : Nat → Bool → Prop}
    (laws : BalanceLaws Eps Push Pop B) (emptyLaws : EmptyLaws Input B R source)
    (q : Nat) (safe : ¬ R q true) (bad : Bool) (run : Trace Eps Push Pop Input source q [] bad) : bad = false := by
  cases bad with
  | false => rfl
  | true => exact False.elim (safe (empty_trace_is_in_table laws emptyLaws q true run))

/- Input/output prefix words project to the operational stack machine. Input
   POP records a required source field; it never invents a concrete transfer.
   Synthetic output draining uses only known-stack POPs, not Input edges. -/
inductive WordTrace (Eps : Binary) (Push Pop Input : Labeled) (source : Nat) :
    Nat → List Nat → List Nat → Prop
  | entry : WordTrace Eps Push Pop Input source source [] []
  | epsilon (p q : Nat) (i o : List Nat) (old : WordTrace Eps Push Pop Input source p i o)
      (edge : Eps p q) : WordTrace Eps Push Pop Input source q i o
  | push (p f q : Nat) (i o : List Nat) (old : WordTrace Eps Push Pop Input source p i o)
      (edge : Push p f q) : WordTrace Eps Push Pop Input source q i (f::o)
  | pop (p f q : Nat) (i o : List Nat) (old : WordTrace Eps Push Pop Input source p i (f::o))
      (edge : Pop p f q) : WordTrace Eps Push Pop Input source q i o
  | input (p f q : Nat) (i : List Nat) (old : WordTrace Eps Push Pop Input source p i [])
      (edge : Input p f q) : WordTrace Eps Push Pop Input source q (i++[f]) []

def debt (input : List Nat) : Bool := !input.isEmpty

theorem word_trace_projects {Eps : Binary} {Push Pop Input : Labeled}
    (q : Nat) (i o : List Nat) (run : WordTrace Eps Push Pop Input source q i o) :
    Trace Eps Push Pop Input source q o (debt i) := by
  induction run with
  | entry => exact Trace.start
  | epsilon p q i o old edge ih => exact Trace.next p q o o (debt i) (debt i) ih (Move.epsilon p q o (debt i) edge)
  | push p f q i o old edge ih => exact Trace.next p q o (f::o) (debt i) (debt i) ih (Move.push p f q o (debt i) edge)
  | pop p f q i o old edge ih => exact Trace.next p q (f::o) o (debt i) (debt i) ih (Move.pop p f q o (debt i) edge)
  | input p f q i old edge ih =>
    have yes : debt (i++[f]) = true := by simp [debt]
    rw [yes]
    exact Trace.next p q [] [] (debt i) true ih (Move.input p f q (debt i) edge)

theorem drain_known_stack {Eps : Binary} {Push Pop Input : Labeled}
    (sink : Nat) (allPops : ∀ f, Pop sink f sink) (i o : List Nat)
    (run : WordTrace Eps Push Pop Input source sink i o) :
    WordTrace Eps Push Pop Input source sink i [] := by
  induction o with
  | nil => exact run
  | cons f rest ih => exact ih (WordTrace.pop sink f sink i rest run (allPops f))

theorem all_output_stacks_have_empty_input {Eps : Binary} {Push Pop Input : Labeled}
    {B : Binary} {R : Nat → Bool → Prop}
    (laws : BalanceLaws Eps Push Pop B) (emptyLaws : EmptyLaws Input B R source)
    (sink : Nat) (safe : ¬ R sink true) (allPops : ∀ f, Pop sink f sink)
    (q : Nat) (toSink : Eps q sink) (i o : List Nat)
    (run : WordTrace Eps Push Pop Input source q i o) : i = [] := by
  have entered := WordTrace.epsilon q sink i o run toSink
  have drained := drain_known_stack sink allPops i o entered
  have safeDebt := no_input_pop_at_goal laws emptyLaws sink safe (debt i)
    (word_trace_projects sink i [] drained)
  simpa [debt] using safeDebt

theorem output_has_no_literal_uri {Eps : Binary} {Push Pop Input : Labeled}
    (uri : Nat) (writers : ∀ p f q, Push p f q → f ≠ uri)
    (q : Nat) (i o : List Nat) (run : WordTrace Eps Push Pop Input source q i o) : uri ∉ o := by
  induction run with
  | entry => simp
  | epsilon _ _ _ _ _ _ ih => exact ih
  | push p f q i o old edge ih => simp [ih, Ne.symm (writers p f q edge)]
  | pop _ f _ i o old edge ih =>
    have both : uri ≠ f ∧ uri ∉ o := by simpa only [List.mem_cons, not_or] using ih
    exact both.2
  | input _ _ _ _ _ _ _ => simp

theorem uri_transfer_is_root_correlated {Eps : Binary} {Push Pop Input : Labeled}
    {B : Binary} {R : Nat → Bool → Prop}
    (laws : BalanceLaws Eps Push Pop B) (emptyLaws : EmptyLaws Input B R source)
    (sink : Nat) (safe : ¬ R sink true) (allPops : ∀ f, Pop sink f sink)
    (uri : Nat) (writers : ∀ p f q, Push p f q → f ≠ uri)
    (q : Nat) (toSink : Eps q sink) (i o suffix tail : List Nat)
    (run : WordTrace Eps Push Pop Input source q i o) (output : o++suffix = uri::tail) :
    i++suffix = uri::tail := by
  have inputEmpty := all_output_stacks_have_empty_input laws emptyLaws sink safe allPops q toSink i o run
  have noLiteral := output_has_no_literal_uri uri writers q i o run
  have outputEmpty : o = [] := by
    cases o with
    | nil => rfl
    | cons f rest =>
      have equal : f = uri := (List.cons.inj output).1
      exact False.elim (noLiteral (by simp [equal]))
  simpa [inputEmpty,outputEmpty] using output

end BalancedPrefixOriginCandidate
#print axioms BalancedPrefixOriginCandidate.advance
#print axioms BalancedPrefixOriginCandidate.pop_known
#print axioms BalancedPrefixOriginCandidate.pop_input
#print axioms BalancedPrefixOriginCandidate.move_preserves
#print axioms BalancedPrefixOriginCandidate.trace_has_state
#print axioms BalancedPrefixOriginCandidate.empty_trace_is_in_table
#print axioms BalancedPrefixOriginCandidate.no_input_pop_at_goal
#print axioms BalancedPrefixOriginCandidate.word_trace_projects
#print axioms BalancedPrefixOriginCandidate.drain_known_stack
#print axioms BalancedPrefixOriginCandidate.all_output_stacks_have_empty_input
#print axioms BalancedPrefixOriginCandidate.output_has_no_literal_uri
#print axioms BalancedPrefixOriginCandidate.uri_transfer_is_root_correlated

/- An internal genuine word can never consume its first URI accessor when
   no native input-POP has that label. No AP MAY premise is assumed here. -/
namespace BalancedPrefixOriginCandidate
theorem input_has_no_literal_uri {Eps : Binary} {Push Pop Input : Labeled}
    (uri : Nat) (readers : ∀ p f q, Input p f q → f ≠ uri)
    (q : Nat) (i o : List Nat) (run : WordTrace Eps Push Pop Input source q i o) : uri ∉ i := by
  induction run with
  | entry => simp
  | epsilon _ _ _ _ _ _ ih => exact ih
  | push _ _ _ _ _ _ _ ih => exact ih
  | pop _ _ _ _ _ _ _ ih => exact ih
  | input p f q i old edge ih => simp [ih, Ne.symm (readers p f q edge)]

theorem initial_uri_is_not_consumed {Eps : Binary} {Push Pop Input : Labeled}
    (uri : Nat) (readers : ∀ p f q, Input p f q → f ≠ uri)
    (q : Nat) (i o suffix tail : List Nat)
    (run : WordTrace Eps Push Pop Input source q i o) (initial : i++suffix = uri::tail) :
    i = [] ∧ suffix = uri::tail := by
  have noUri := input_has_no_literal_uri uri readers q i o run
  have noInput : i = [] := by
    cases i with
    | nil => rfl
    | cons f rest =>
      have first : f = uri := (List.cons.inj initial).1
      exact False.elim (noUri (by simp [first]))
  exact ⟨noInput, by simpa [noInput] using initial⟩

theorem uri_input_stays_nonroot {Eps : Binary} {Push Pop Input : Labeled}
    (uri : Nat) (readers : ∀ p f q, Input p f q → f ≠ uri)
    (q : Nat) (i o suffix tail : List Nat)
    (run : WordTrace Eps Push Pop Input source q i o) (initial : i++suffix = uri::tail) :
    o++suffix ≠ [] := by
  have intact := (initial_uri_is_not_consumed uri readers q i o suffix tail run initial).2
  simp [intact]
end BalancedPrefixOriginCandidate
#print axioms BalancedPrefixOriginCandidate.input_has_no_literal_uri
#print axioms BalancedPrefixOriginCandidate.initial_uri_is_not_consumed
#print axioms BalancedPrefixOriginCandidate.uri_input_stays_nonroot
