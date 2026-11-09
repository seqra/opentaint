/-
# Choosing the join target by the DEMAND, not by arrival order

`Relocation` proves that a context join costs a CROSS PRODUCT: the merged slot holds the union of the
facts and answers the union of the demands, so every merged fact meets every merged demand
(`Relocation.join_is_a_cross_product`), and it costs nothing when the demands already agree
(`Relocation.join_is_free_when_the_demand_is_shared`).

The shipped cap chooses its target by ARRIVAL ORDER -- the deepest ancestor that happens to exist.
This module states the alternative and proves the three things a policy has to satisfy:

* it never loses an answer, whatever it chooses (`choice_is_sound_for_any_target`,
  `runAll_never_loses`);
* it holds the population at the budget, whatever it chooses (`runAll_bounded`);
* the CHOICE decides the cost and nothing else (`answers_after_join`, `demand_choice_is_cheaper`).

So the policy is a pure cost decision. `answers_after_join` is what makes it safe to change DURING a
run: the join target is not part of any fact's meaning, which is exactly what
`Adaptive.switch_during_the_run_loses_a_fact` denies to a fact budget.

The measured warrant for building it: at cap 100, joining into the ROOT gave `premisePair`
1,089,037; joining into the deepest existing ancestor at cap 1000 gave 243,740. The choice already
moved the cost 4.5x, and neither rule looks at the demand at all.
-/

namespace FactExplosion.Subscribe

abbrev Acc := Nat
abbrev Path := List Acc

def pathEq : Path → Path → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | x :: xs, y :: ys => Nat.beq x y && pathEq xs ys

def mem (p : Path) : List Path → Bool
  | [] => false
  | q :: r => pathEq q p || mem p r

theorem or_swap (a b c : Bool) : ((a || b) || c) = ((a || c) || b) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem or_assoc' (a b c : Bool) : ((a || b) || c) = (a || (b || c)) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The demand of a slot is a SET: a question already asked is not asked twice. -/
def addNew (l : List Path) : List Path → List Path
  | [] => l
  | p :: r => addNew (cond (mem p l) l (l ++ [p])) r

theorem mem_append_eq : ∀ (l m : List Path) (p : Path),
    mem p (l ++ m) = (mem p l || mem p m) := by
  intro l
  induction l with
  | nil => intro m p; rfl
  | cons q r ih =>
      intro m p
      show (pathEq q p || mem p (r ++ m)) = ((pathEq q p || mem p r) || mem p m)
      rw [ih m p, or_assoc']

/--
One context of a callee: the initial access path that names it, the final facts stored under it, and
the questions the analysis has asked about it.
-/
structure Context where
  key : Path
  facts : List Path
  demand : List Path

/-- The callee's state for one fact base. -/
abbrev State := List Context

def population (s : State) : Nat := s.length

/--
The ancestor reader of `ContextCap` answers a query from every context on the root-to-key path. Here
the same thing is stated as: a state answers `p` when SOME context answers it. That is all the
soundness argument needs, and it is what makes a join invisible to a reader.
-/
def answers (s : State) (p : Path) : Bool := s.any (fun c => mem p c.facts)

def hasKey (t : Path) : State → Bool
  | [] => false
  | c :: r => pathEq c.key t || hasKey t r

/-! ## The join -/

def joinInto (target : Path) (f d : List Path) : State → State
  | [] => []
  | c :: r =>
      cond (pathEq c.key target)
        ({ key := c.key, facts := c.facts ++ f, demand := addNew c.demand d } :: r)
        (c :: joinInto target f d r)

/--
**What a join answers, in closed form.** For a target that exists, the state afterwards answers
exactly what it answered before, plus the arriving fact. The TARGET DOES NOT APPEAR on the right, so
two policies that pick different existing targets are indistinguishable to every reader.
-/
theorem answers_after_join (t : Path) (f d : List Path) :
    ∀ (s : State) (p : Path), hasKey t s = true →
      answers (joinInto t f d s) p = (answers s p || mem p f) := by
  intro s
  induction s with
  | nil => intro p h; exact Bool.noConfusion h
  | cons c r ih =>
      intro p h
      show answers (cond (pathEq c.key t)
            ({ key := c.key, facts := c.facts ++ f, demand := addNew c.demand d } :: r)
            (c :: joinInto t f d r)) p
          = ((mem p c.facts || answers r p) || mem p f)
      cases hk : pathEq c.key t with
      | true =>
          show (mem p (c.facts ++ f) || answers r p) = ((mem p c.facts || answers r p) || mem p f)
          rw [mem_append_eq c.facts f p]
          exact or_swap _ _ _
      | false =>
          have hr : hasKey t r = true := by
            have h' : (pathEq c.key t || hasKey t r) = true := h
            rw [hk] at h'
            exact h'
          show (mem p c.facts || answers (joinInto t f d r) p)
              = ((mem p c.facts || answers r p) || mem p f)
          rw [ih p hr, or_assoc']

/-- **A join never removes an answer.** Whatever target it picks, existing or not. -/
theorem join_never_loses (t : Path) (f d : List Path) :
    ∀ (s : State) (p : Path), answers s p = true → answers (joinInto t f d s) p = true := by
  intro s
  induction s with
  | nil => intro p h; exact h
  | cons c r ih =>
      intro p h
      have h' : (mem p c.facts || answers r p) = true := h
      show answers (cond (pathEq c.key t)
            ({ key := c.key, facts := c.facts ++ f, demand := addNew c.demand d } :: r)
            (c :: joinInto t f d r)) p = true
      cases hk : pathEq c.key t with
      | true =>
          show (mem p (c.facts ++ f) || answers r p) = true
          rw [mem_append_eq c.facts f p, or_assoc']
          cases hc : mem p c.facts with
          | true => rfl
          | false =>
              rw [hc] at h'
              have : answers r p = true := h'
              rw [this]
              cases mem p f <;> rfl
      | false =>
          show (mem p c.facts || answers (joinInto t f d r) p) = true
          cases hc : mem p c.facts with
          | true => rfl
          | false =>
              rw [hc] at h'
              have hr : answers r p = true := h'
              rw [ih p hr]
              exact Bool.or_true _

/-- **A join never changes the population.** It writes into a context that already exists. -/
theorem join_keeps_population (t : Path) (f d : List Path) :
    ∀ s : State, population (joinInto t f d s) = population s := by
  intro s
  induction s with
  | nil => rfl
  | cons c r ih =>
      show population (cond (pathEq c.key t)
            ({ key := c.key, facts := c.facts ++ f, demand := addNew c.demand d } :: r)
            (c :: joinInto t f d r)) = population (c :: r)
      cases hk : pathEq c.key t with
      | true => rfl
      | false =>
          show population (joinInto t f d r) + 1 = population r + 1
          rw [ih]

/-! ## The policy

A policy only chooses WHERE to join. It cannot choose whether to join, and it cannot choose to drop.
That is the whole point: the choice is a cost decision.
-/

abbrev Policy := State → Path → List Path → Path

/-- One arrival: below the budget it is a new context, at the budget it joins where the policy says. -/
def arrive (P : Policy) (N : Nat) (s : State) (key : Path) (f d : List Path) : State :=
  cond (decide (population s < N))
    ({ key := key, facts := f, demand := d } :: s)
    (joinInto (P s key f) f d s)

/-- **Whatever the policy chooses, nothing already answered stops being answered.** -/
theorem choice_is_sound_for_any_target (P : Policy) (N : Nat) (s : State)
    (key : Path) (f d : List Path) (p : Path) (h : answers s p = true) :
    answers (arrive P N s key f d) p = true := by
  show answers (cond (decide (population s < N))
        ({ key := key, facts := f, demand := d } :: s)
        (joinInto (P s key f) f d s)) p = true
  cases hb : decide (population s < N) with
  | true =>
      show (mem p f || answers s p) = true
      rw [h]
      exact Bool.or_true _
  | false =>
      show answers (joinInto (P s key f) f d s) p = true
      exact join_never_loses (P s key f) f d s p h

/-- **And the arriving fact is answered**, whichever branch is taken, as long as the target exists. -/
theorem arrival_is_answered (P : Policy) (N : Nat) (s : State)
    (key : Path) (f d : List Path) (p : Path)
    (hkey : hasKey (P s key f) s = true) (h : mem p f = true) :
    answers (arrive P N s key f d) p = true := by
  show answers (cond (decide (population s < N))
        ({ key := key, facts := f, demand := d } :: s)
        (joinInto (P s key f) f d s)) p = true
  cases hb : decide (population s < N) with
  | true =>
      show (mem p f || answers s p) = true
      rw [h]
      rfl
  | false =>
      show answers (joinInto (P s key f) f d s) p = true
      rw [answers_after_join (P s key f) f d s p hkey, h]
      exact Bool.or_true _

/-- **The population never passes the budget.** -/
theorem arrive_bounded (P : Policy) (N : Nat) (s : State) (key : Path) (f d : List Path)
    (h : population s ≤ N) : population (arrive P N s key f d) ≤ N := by
  show population (cond (decide (population s < N))
        ({ key := key, facts := f, demand := d } :: s)
        (joinInto (P s key f) f d s)) ≤ N
  cases hb : decide (population s < N) with
  | true =>
      have hlt : population s < N := of_decide_eq_true hb
      show s.length + 1 ≤ N
      have : population s = s.length := rfl
      omega
  | false =>
      show population (joinInto (P s key f) f d s) ≤ N
      rw [join_keeps_population]
      exact h

def runAll (P : Policy) (N : Nat) (s : State) : List (Path × List Path × List Path) → State
  | [] => s
  | a :: r => runAll P N (arrive P N s a.1 a.2.1 a.2.2) r

/-- **Any number of callers, in any order.** -/
theorem runAll_bounded (P : Policy) (N : Nat) :
    ∀ (as : List (Path × List Path × List Path)) (s : State),
      population s ≤ N → population (runAll P N s as) ≤ N := by
  intro as
  induction as with
  | nil => intro s h; exact h
  | cons a r ih =>
      intro s h
      exact ih (arrive P N s a.1 a.2.1 a.2.2) (arrive_bounded P N s a.1 a.2.1 a.2.2 h)

theorem runAll_never_loses (P : Policy) (N : Nat) :
    ∀ (as : List (Path × List Path × List Path)) (s : State) (p : Path),
      answers s p = true → answers (runAll P N s as) p = true := by
  intro as
  induction as with
  | nil => intro s p h; exact h
  | cons a r ih =>
      intro s p h
      exact ih (arrive P N s a.1 a.2.1 a.2.2) p
        (choice_is_sound_for_any_target P N s a.1 a.2.1 a.2.2 p h)

/-! ## The cost, and why the DEMAND decides it

`Relocation.emitted` charges one premise per fact path the demand reaches. The same charge is made
here per context, so the cost of a state is what the whole slot set emits.
-/

def costOf (c : Context) : Nat := c.facts.length * c.demand.length

def cost (s : State) : Nat := s.foldr (fun c acc => costOf c + acc) 0

/--
**The witness.** Two contexts in the state and one arrival that asks `[9]`. Joining into the context
that ALREADY asks `[9]` costs 3; joining into the one that asks something else costs 5, because the
arriving fact and the resident fact each meet both questions -- the cross product of
`Relocation.join_is_a_cross_product`.
-/
def sSame : State :=
  [ { key := [1], facts := [[1]], demand := [[9]] },
    { key := [2], facts := [[2]], demand := [[8]] } ]

theorem demand_choice_is_cheaper :
    cost (joinInto [1] [[3]] [[9]] sSame) = 3 ∧
    cost (joinInto [2] [[3]] [[9]] sSame) = 5 := by
  constructor <;> decide

/--
**And the two choices are indistinguishable to a reader.** Both targets exist, so `answers_after_join`
gives the same closed form for both. A policy may therefore switch target rule mid-run.
-/
theorem both_choices_answer_the_same (p : Path) :
    answers (joinInto [1] [[3]] [[9]] sSame) p = answers (joinInto [2] [[3]] [[9]] sSame) p := by
  have h1 : hasKey [1] sSame = true := by decide
  have h2 : hasKey [2] sSame = true := by decide
  rw [answers_after_join [1] [[3]] [[9]] sSame p h1,
      answers_after_join [2] [[3]] [[9]] sSame p h2]

end FactExplosion.Subscribe
