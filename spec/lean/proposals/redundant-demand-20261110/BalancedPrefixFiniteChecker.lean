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

namespace BalancedPrefixOriginCandidate.Finite
/- Finite postfixed guard. Binary trees are merely executable lookup maps;
   no ordering axiom is needed. Every successful lookup returns a declared
   key, and the checker scans every declared key, including any duplicates. -/
inductive Set where
  | nil
  | node (key : Nat) (left right : Set)
  deriving Repr
namespace Set
def keys : Set → List Nat
  | .nil => []
  | .node k l r => k :: (keys l ++ keys r)
def has : Set → Nat → Bool
  | .nil, _ => false
  | .node k l r, q => if q = k then true else if q < k then has l q else has r q
def every (f : Nat → Bool) : Set → Bool
  | .nil => true
  | .node k l r => f k && (every f l && every f r)
theorem has_key (s : Set) (q : Nat) (h : s.has q = true) : q ∈ s.keys := by
  induction s with
  | nil => simp [has] at h
  | node k l r il ir =>
    by_cases same : q = k
    · simp [keys, same]
    · by_cases less : q < k
      · have inner : l.has q = true := by simpa [has,same,less] using h
        exact List.mem_cons_of_mem k (List.mem_append_left _ (il inner))
      · have inner : r.has q = true := by simpa [has,same,less] using h
        exact List.mem_cons_of_mem k (List.mem_append_right _ (ir inner))
theorem every_key (s : Set) (f : Nat → Bool) (h : s.every f = true) (q : Nat) (member : q ∈ s.keys) : f q = true := by
  induction s with
  | nil => simp [keys] at member
  | node k l r il ir =>
    simp only [every, Bool.and_eq_true] at h
    simp only [keys, List.mem_cons, List.mem_append] at member
    rcases member with same | left | right
    · simpa only [same] using h.1
    · exact il h.2.1 left
    · exact ir h.2.2 right
end Set

inductive Rows where
  | nil
  | node (key : Nat) (values : Set) (left right : Rows)
  deriving Repr
namespace Rows
def entries : Rows → List (Nat × Set)
  | .nil => []
  | .node k v l r => (k,v) :: (entries l ++ entries r)
def get : Rows → Nat → Set
  | .nil, _ => .nil
  | .node k v l r, p => if Nat.beq p k then v else if Nat.blt p k then get l p else get r p
def every (f : Nat → Set → Bool) : Rows → Bool
  | .nil => true
  | .node k v l r => f k v && (every f l && every f r)
/- The structural certificate composes already checked rows without forcing
   the kernel to reevaluate the whole closed Boolean during elaboration. -/
inductive All (f : Nat → Set → Bool) : Rows → Prop
  | nil : All f .nil
  | node (key : Nat) (values : Set) (left right : Rows)
      (here : f key values = true) (belowLeft : All f left) (belowRight : All f right) :
      All f (.node key values left right)
theorem All.checked {f : Nat → Set → Bool} {rows : Rows} (proof : All f rows) : rows.every f = true := by
  induction proof with
  | nil => rfl
  | node k v l r here belowLeft belowRight il ir => simp only [every,here,il,ir,Bool.and_self]
theorem get_member (rows : Rows) (p q : Nat) (member : q ∈ (rows.get p).keys) :
    ∃ values, (p,values) ∈ rows.entries ∧ q ∈ values.keys := by
  induction rows with
  | nil => simp [get,Set.keys] at member
  | node k values l r il ir =>
    by_cases same : p=k
    · subst p
      exact ⟨values,by simp [entries],by simpa [get] using member⟩
    · by_cases less : p<k
      · have inner : q ∈ (l.get p).keys := by simpa [get,same,less] using member
        rcases il inner with ⟨v,hp,hq⟩
        exact ⟨v,List.mem_cons_of_mem _ (List.mem_append_left _ hp),hq⟩
      · have inner : q ∈ (r.get p).keys := by simpa [get,same,less] using member
        rcases ir inner with ⟨v,hp,hq⟩
        exact ⟨v,List.mem_cons_of_mem _ (List.mem_append_right _ hp),hq⟩
theorem every_entry (rows : Rows) (f : Nat → Set → Bool) (h : rows.every f = true)
    (p : Nat) (values : Set) (member : (p,values) ∈ rows.entries) : f p values = true := by
  induction rows with
  | nil => simp [entries] at member
  | node k v l r il ir =>
    simp only [every,Bool.and_eq_true] at h
    simp only [entries,List.mem_cons,List.mem_append] at member
    rcases member with same | left | right
    · cases same
      exact h.1
    · exact il h.2.1 left
    · exact ir h.2.2 right
end Rows

def hasB (rows : Rows) (p q : Nat) : Bool := Nat.beq p q || (rows.get p).has q
def relation (rows : Rows) (p q : Nat) : Prop := hasB rows p q = true

def checkTrans (rows : Rows) : Bool :=
  rows.every fun p values => values.every fun q => (rows.get q).every fun r => hasB rows p r

theorem checked_trans (rows : Rows) (checked : checkTrans rows = true)
    (p q r : Nat) (pq : relation rows p q) (qr : relation rows q r) : relation rows p r := by
  by_cases same : p=q
  · simpa only [same] using qr
  by_cases same2 : q=r
  · simpa only [same2] using pq
  have pMem : q ∈ (rows.get p).keys := Set.has_key _ _ (by simpa [relation,hasB,same] using pq)
  have qMem : r ∈ (rows.get q).keys := Set.has_key _ _ (by simpa [relation,hasB,same2] using qr)
  rcases Rows.get_member rows p q pMem with ⟨values,entry,member⟩
  have rowCheck := Rows.every_entry rows _ checked p values entry
  have childCheck := Set.every_key values _ rowCheck q member
  exact Set.every_key (rows.get q) _ childCheck r qMem

structure PushEdge where
  source : Nat
  label : Nat
  dest : Nat
  deriving DecidableEq, Repr
structure PopEdge where
  source : Nat
  label : Nat
  dest : Nat
  input : Bool
  deriving DecidableEq, Repr
structure Graph where
  eps : List (Nat × Nat)
  pushes : List PushEdge
  pops : List PopEdge
  /- A fresh synthetic sink can drain arbitrary known output fields.
     It is never an unmatched-input POP. -/
  drain : Nat
  deriving Repr

def Eps (g : Graph) (p q : Nat) := (p,q) ∈ g.eps
def Push (g : Graph) (p f q : Nat) := PushEdge.mk p f q ∈ g.pushes
def Pop (g : Graph) (p f q : Nat) :=
  (∃ allowed, PopEdge.mk p f q allowed ∈ g.pops) ∨ (p = g.drain ∧ q = g.drain)
def Input (g : Graph) (p f q : Nat) := PopEdge.mk p f q true ∈ g.pops

def checkEps (g : Graph) (rows : Rows) : Bool := g.eps.all fun e => hasB rows e.1 e.2
def checkWrap (g : Graph) (rows : Rows) : Bool :=
  g.pushes.all fun push => g.pops.all fun pop =>
    if (Nat.beq push.label pop.label) && hasB rows push.dest pop.source then hasB rows push.source pop.dest else true
def checkDrainWrap (g : Graph) (rows : Rows) : Bool :=
  g.pushes.all fun push => !hasB rows push.dest g.drain || hasB rows push.source g.drain

theorem checked_balance (g : Graph) (rows : Rows) (trans : checkTrans rows = true)
    (eps : checkEps g rows = true) (wrap : checkWrap g rows = true)
    (drain : checkDrainWrap g rows = true) :
    BalanceLaws (Eps g) (Push g) (Pop g) (relation rows) where
  refl q := by simp [relation,hasB]
  epsilon p q edge := (List.all_eq_true.mp eps) _ edge
  trans p q r left right := checked_trans rows trans p q r left right
  wrap p f a b q push inside pop := by
    rcases pop with finite | synthetic
    · rcases finite with ⟨allowed,member⟩
      have first := (List.all_eq_true.mp wrap) _ push
      have second := (List.all_eq_true.mp first) _ member
      have inner : hasB rows a b = true := inside
      change (if Nat.beq f f && hasB rows a b then hasB rows p q else true) = true at second
      rw [Nat.beq_refl, Bool.true_and, inner] at second
      exact second
    · rcases synthetic with ⟨rfl,rfl⟩
      have h := (List.all_eq_true.mp drain) _ push
      have inner : hasB rows a g.drain = true := inside
      simpa [relation,inner] using h

def result (good bad : Set) (q : Nat) (debt : Bool) : Prop := (if debt then bad else good).has q = true

def checkMove (rows : Rows) (store : Set) : Bool :=
  store.every fun p => (rows.get p).every fun q => store.has q

def checkInput (g : Graph) (good bad : Set) : Bool :=
  g.pops.all fun e => if e.input then
    (!good.has e.source || bad.has e.dest) && (!bad.has e.source || bad.has e.dest)
    else true

theorem checked_result_move (rows : Rows) (store : Set) (checked : checkMove rows store = true)
    (p q : Nat) (before : store.has p = true) (segment : relation rows p q) : store.has q = true := by
  by_cases same : p=q
  · simpa only [same] using before
  have pMember := Set.has_key store p before
  have rowCheck := Set.every_key store _ checked p pMember
  have qMember := Set.has_key _ _ (by simpa [relation,hasB,same] using segment)
  exact Set.every_key _ _ rowCheck q qMember

theorem checked_empty (g : Graph) (rows : Rows) (good bad : Set) (source : Nat)
    (entry : good.has source = true) (moveGood : checkMove rows good = true)
    (moveBad : checkMove rows bad = true) (input : checkInput g good bad = true) :
    EmptyLaws (Input g) (relation rows) (result good bad) source where
  entry := entry
  balanced p q debt before segment := by
    cases debt with
    | false => exact checked_result_move rows good moveGood p q before segment
    | true => exact checked_result_move rows bad moveBad p q before segment
  input p f q debt before edge := by
    have h := (List.all_eq_true.mp input) _ edge
    have parts : (!good.has p || bad.has q) = true ∧ (!bad.has p || bad.has q) = true := by
      simpa only [ite_true,Bool.and_eq_true] using h
    cases debt with
    | false =>
      have hp : good.has p = true := before
      simpa [result,hp] using parts.1
    | true =>
      have hp : bad.has p = true := before
      simpa [result,hp] using parts.2
end BalancedPrefixOriginCandidate.Finite
#print axioms BalancedPrefixOriginCandidate.Finite.Set.has_key
#print axioms BalancedPrefixOriginCandidate.Finite.Set.every_key
#print axioms BalancedPrefixOriginCandidate.Finite.Rows.get_member
#print axioms BalancedPrefixOriginCandidate.Finite.Rows.every_entry
#print axioms BalancedPrefixOriginCandidate.Finite.checked_trans
#print axioms BalancedPrefixOriginCandidate.Finite.checked_balance
#print axioms BalancedPrefixOriginCandidate.Finite.checked_result_move
#print axioms BalancedPrefixOriginCandidate.Finite.checked_empty
