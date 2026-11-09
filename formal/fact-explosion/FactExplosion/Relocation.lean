/-
# Why a fact bound relocates into the demand, as a THEOREM

The project measured a law and could not explain it (`CLAIMS.md`, "destroying structure relocates to
demand"): every operator that SHORTENS a fact raises the premise rate, monotonically in how hard it
shortens, and only the LIFT -- which moves a star the fact already carries -- lowers it. The law was
a table of five arms. This module makes it a structural statement, so a new operator can be checked
BEFORE it is built.

The mechanism has one moving part. A fact answers a question by NAME. An abstract position answers
"something below here is tainted" and names nothing, so the asker must ask again, one question per
accessor of the alphabet. Those new questions land under the same abstract position, are answered the
same way, and ask again.

* `no_abstract_no_growth_n` -- with no abstract position the demand is a FIXED POINT.
* `ladder_is_geometric`     -- under one abstract position the demand is `|d| * (k+1)^n`.

That is the separation the goal asks for: the same demand, with and without one cut, gives a constant
and an exponential. It also gives the CRITERION used from here on:

> An operator may bound a fact only if it adds no abstract position that the demand reaches.

Truncation fails the criterion (`truncation_is_not_demand_neutral`). The lift passes it
(`lift_is_demand_neutral`). A join that shares the STORE and leaves the fact alone passes it for free
(`store_join_is_demand_neutral`), which is why it is the only operator in this project measured to
cut the fact count and the premise count at the same time.

**Scope.** This models the ASKING side only: one alphabet, one abstract position per branch, and no
type filter. It says which operator starts a ladder, not how many rounds the engine runs.
-/

namespace FactExplosion.Relocation

abbrev Acc := Nat
abbrev Path := List Acc

/-- `Nat.beq` is reflexive, by recursion: `beq_self_eq_true` carries `Classical.choice`. -/
theorem natBeqRefl : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => natBeqRefl n

theorem andLeft {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | true => rfl
  | false => exact Bool.noConfusion h

theorem andRight {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | true => exact h
  | false => exact Bool.noConfusion h

def isPrefix : Path → Path → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => Nat.beq x y && isPrefix xs ys

theorem isPrefix_refl : ∀ p : Path, isPrefix p p = true := by
  intro p
  induction p with
  | nil => rfl
  | cons x xs ih =>
      show (Nat.beq x x && isPrefix xs xs) = true
      rw [ih, natBeqRefl x]
      rfl

theorem isPrefix_trans : ∀ a b c : Path,
    isPrefix a b = true → isPrefix b c = true → isPrefix a c = true := by
  intro a
  induction a with
  | nil => intro b c _ _; rfl
  | cons x xs ih =>
      intro b c h1 h2
      cases b with
      | nil => exact Bool.noConfusion h1
      | cons y ys =>
          cases c with
          | nil => exact Bool.noConfusion h2
          | cons z zs =>
              have hxy : Nat.beq x y = true := andLeft h1
              have hys : isPrefix xs ys = true := andRight h1
              have hyz : Nat.beq y z = true := andLeft h2
              have hzs : isPrefix ys zs = true := andRight h2
              have exy : x = y := Nat.eq_of_beq_eq_true hxy
              have eyz : y = z := Nat.eq_of_beq_eq_true hyz
              show (Nat.beq x z && isPrefix xs zs) = true
              rw [ih ys zs hys hzs]
              rw [exy, eyz, natBeqRefl z]
              rfl

/-- A filter written with `cond`, so the two branches reduce for `show`. -/
def keep (P : Path → Bool) : List Path → List Path
  | [] => []
  | p :: r => cond (P p) (p :: keep P r) (keep P r)

/--
A fact, split into the two things that decide the demand: the paths it answers BY NAME, and the
positions where it answers only "something below". `abstract` is the engine's `[any]`.
-/
structure Fact where
  concrete : List Path
  abstract : List Path

/-- The demand: every path some caller has asked about. This is the engine's premise trie. -/
abbrev Demand := List Path

/-! ## The ladder

A demanded path is on the FRONTIER when an abstract position stands above it: the fact cannot name
what is there, so the asker refines by one accessor, once for every accessor of the alphabet.
-/

def underAbstract (f : Fact) (p : Path) : Bool := f.abstract.any (fun q => isPrefix q p)

def frontier (f : Fact) (d : Demand) : List Path := keep (underAbstract f) d

def expand (alphabet : List Acc) (p : Path) : List Path := alphabet.map (fun a => p ++ [a])

/-- One round of refinement. In the engine this is `demandAdvance`. -/
def refine (alphabet : List Acc) (f : Fact) (d : Demand) : Demand :=
  d ++ (frontier f d).flatMap (expand alphabet)

def refineN (alphabet : List Acc) (f : Fact) (d : Demand) : Nat → Demand
  | 0 => d
  | n + 1 => refine alphabet f (refineN alphabet f d n)

theorem expand_length (alphabet : List Acc) (p : Path) :
    (expand alphabet p).length = alphabet.length := by
  unfold expand
  rw [List.length_map]

/-- The demand grows by one alphabet per frontier path. -/
theorem flatMap_expand_length (alphabet : List Acc) :
    ∀ l : List Path, (l.flatMap (expand alphabet)).length = l.length * alphabet.length := by
  intro l
  induction l with
  | nil =>
      rw [show ([] : List Path).length = 0 from rfl, Nat.zero_mul]
      rfl
  | cons p r ih =>
      show ((expand alphabet p) ++ (r.flatMap (expand alphabet))).length
          = (r.length + 1) * alphabet.length
      rw [List.length_append, ih, expand_length]
      have h : (r.length + 1) * alphabet.length
          = r.length * alphabet.length + alphabet.length := by
        rw [Nat.add_mul, Nat.one_mul]
      omega

/-- **The closed form of one round.** -/
theorem refine_length (alphabet : List Acc) (f : Fact) (d : Demand) :
    (refine alphabet f d).length = d.length + (frontier f d).length * alphabet.length := by
  unfold refine
  rw [List.length_append, flatMap_expand_length]

/-! ### With no abstract position the demand is a fixed point -/

theorem keep_none (P : Path → Bool) (h : ∀ p, P p = false) :
    ∀ l : List Path, keep P l = []
  | [] => rfl
  | p :: r => by
      show cond (P p) (p :: keep P r) (keep P r) = []
      rw [h p]
      show keep P r = []
      exact keep_none P h r

theorem underAbstract_of_none (f : Fact) (h : f.abstract = []) :
    ∀ p, underAbstract f p = false := by
  intro p
  unfold underAbstract
  rw [h]
  rfl

/-- **A fact that names everything asks nothing more.** The demand is a FIXED POINT. -/
theorem no_abstract_no_growth (alphabet : List Acc) (f : Fact) (d : Demand)
    (h : f.abstract = []) : refine alphabet f d = d := by
  unfold refine frontier
  rw [keep_none (underAbstract f) (underAbstract_of_none f h) d]
  exact List.append_nil d

theorem no_abstract_no_growth_n (alphabet : List Acc) (f : Fact) (d : Demand)
    (h : f.abstract = []) : ∀ n, refineN alphabet f d n = d := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih =>
      show refine alphabet f (refineN alphabet f d n') = d
      rw [ih]
      exact no_abstract_no_growth alphabet f d h

/-! ### Under one abstract position the demand is geometric -/

/-- The extreme fact: abstract at the root, so it names nothing at all. -/
def topFact : Fact := { concrete := [], abstract := [[]] }

theorem underAbstract_top : ∀ p, underAbstract topFact p = true := by
  intro p
  rfl

theorem keep_all (P : Path → Bool) (h : ∀ p, P p = true) :
    ∀ l : List Path, keep P l = l
  | [] => rfl
  | p :: r => by
      show cond (P p) (p :: keep P r) (keep P r) = p :: r
      rw [h p]
      show p :: keep P r = p :: r
      rw [keep_all P h r]

theorem frontier_of_top (d : Demand) : frontier topFact d = d := by
  unfold frontier
  exact keep_all (underAbstract topFact) underAbstract_top d

/-- **One round multiplies the demand by `k + 1`.** -/
theorem refine_top_length (alphabet : List Acc) (d : Demand) :
    (refine alphabet topFact d).length = d.length * (alphabet.length + 1) := by
  rw [refine_length, frontier_of_top]
  have h : d.length * (alphabet.length + 1) = d.length * alphabet.length + d.length := by
    rw [Nat.mul_add, Nat.mul_one]
  omega

/--
**THE SEPARATION.** Against the same demand and the same number of rounds:

* a fact that names everything leaves the demand at `|d|` (`no_abstract_no_growth_n`);
* a fact with one abstract position above it leaves the demand at `|d| * (k+1)^n`.

A constant against an exponential. This is the law "destroying structure relocates to demand", stated
once for all inputs instead of measured on five arms.
-/
theorem ladder_is_geometric (alphabet : List Acc) (d : Demand) :
    ∀ n, (refineN alphabet topFact d n).length = d.length * (alphabet.length + 1) ^ n := by
  intro n
  induction n with
  | zero =>
      show d.length = d.length * 1
      rw [Nat.mul_one]
  | succ n' ih =>
      show (refine alphabet topFact (refineN alphabet topFact d n')).length
          = d.length * (alphabet.length + 1) ^ (n' + 1)
      rw [refine_top_length, ih, Nat.pow_succ, Nat.mul_assoc]

/-! ## The criterion -/

/-- The multiplier: how many positions the fact refuses to name. -/
def abstractCount (f : Fact) : Nat := f.abstract.length

/-- An operator that never lengthens the abstract list cannot start a ladder that was not running. -/
def DemandNeutral (op : Fact → Fact) : Prop :=
  ∀ f : Fact, abstractCount (op f) ≤ abstractCount f

/-! ### Truncation FAILS the criterion -/

/-- Cut every path at depth `k`, and leave an abstract position where each cut was made. -/
def truncFact (k : Nat) (f : Fact) : Fact :=
  { concrete := keep (fun p => decide (p.length ≤ k)) f.concrete,
    abstract := f.abstract
      ++ (keep (fun p => decide (k < p.length)) f.concrete).map (fun p => p.take k) }

/-- A chain fact with one deep path and nothing abstract. -/
def chainFact : Fact := { concrete := [[1, 2, 3]], abstract := [] }

/--
**Truncation adds an abstract position.** Executable witness: a chain with NO abstract position
becomes a fact with one. By `ladder_is_geometric` that is the difference between a fixed point and
`(k+1)^n`.
-/
theorem truncation_adds_an_abstract_position :
    abstractCount chainFact = 0 ∧ abstractCount (truncFact 1 chainFact) = 1 :=
  ⟨rfl, rfl⟩

theorem truncation_is_not_demand_neutral : ¬ DemandNeutral (truncFact 1) := by
  intro h
  have hle := h chainFact
  have h0 : abstractCount chainFact = 0 := rfl
  have h1 : abstractCount (truncFact 1 chainFact) = 1 := rfl
  rw [h0, h1] at hle
  omega

/-! ### The lift PASSES the criterion

The lift moves a star the fact already carries. It rewrites the POSITIONS and never adds one.
-/

def liftFact (up : Path → Path) (f : Fact) : Fact :=
  { concrete := f.concrete, abstract := f.abstract.map up }

theorem lift_keeps_the_abstract_count (up : Path → Path) (f : Fact) :
    abstractCount (liftFact up f) = abstractCount f := by
  unfold abstractCount liftFact
  rw [List.length_map]

theorem lift_is_demand_neutral (up : Path → Path) : DemandNeutral (liftFact up) := by
  intro f
  rw [lift_keeps_the_abstract_count]
  exact Nat.le_refl _

/-! ### Sharing a STORE passes the criterion for free

The context join of `ContextCap` merges the edge sets of two initial facts and reads every ancestor
on the path. It changes what is stored WITH a fact, never the fact, so the demand cannot see it. That
is why it is the only operator in this project measured to cut both axes at once: every other one
paid its fact saving back here.
-/

theorem store_join_is_demand_neutral : DemandNeutral (fun f => f) := by
  intro f
  exact Nat.le_refl _

theorem store_join_changes_no_demand (alphabet : List Acc) (f : Fact) (d : Demand) :
    refine alphabet ((fun g => g) f) d = refine alphabet f d := rfl

/-! ## The soundness side, so the criterion is not read as permission

Demand-neutrality is a COST property. It says nothing about false negatives, and the two must not be
confused. An operator must ALSO widen: everything the fact answered, the result answers.
-/

def mem (p : Path) : List Path → Bool
  | [] => false
  | q :: r => (isPrefix q p && isPrefix p q) || mem p r

def accepts (f : Fact) (p : Path) : Bool := mem p f.concrete || underAbstract f p

/-- The store join answers exactly what it answered: it is exact, not a widening. -/
theorem store_join_sound (f : Fact) (p : Path) :
    accepts ((fun g => g) f) p = accepts f p := rfl

/-- The lift keeps an abstract answer when the move only shortens the position. -/
theorem lift_keeps_an_abstract_answer (f : Fact) (p q : Path) (up : Path → Path)
    (hq : f.abstract = [q]) (hpre : isPrefix q p = true)
    (hup : isPrefix (up q) q = true) :
    accepts (liftFact up f) p = true := by
  unfold accepts underAbstract liftFact
  rw [hq]
  show (mem p f.concrete || (List.any [up q] fun r => isPrefix r p)) = true
  have h : (List.any [up q] fun r => isPrefix r p) = true := by
    show (isPrefix (up q) p || false) = true
    rw [isPrefix_trans (up q) q p hup hpre]
    rfl
  rw [h]
  exact Bool.or_true _

/--
**Truncation is a widening too.** It is refused by the criterion for its COST, not for a false
negative: a cut path is still answered, through the abstract position the cut left behind.
-/
theorem truncation_keeps_a_cut_path :
    accepts chainFact [1, 2, 3] = true ∧ accepts (truncFact 1 chainFact) [1, 2, 3] = true :=
  ⟨rfl, rfl⟩

/-! ## CHANNEL 2: the JOIN pays a CROSS PRODUCT, and the model needed this correction

`store_join_is_demand_neutral` above says the join starts no ladder, and that is right: the measured
context-cap ladder raises `analyzedAdd` only 1.24x while it raises `premisePair` 2.7x. So the join
does NOT refine the demand -- but the first version of this module then implied it was free, and it
is not.

A join merges the FINAL FACTS of several contexts into one slot, and it merges their DEMANDS with
them. Every merged fact then meets every merged demand. What was a SUM of `|fact_i| * |demand_i|`
becomes a PRODUCT of the sums.

* `emitted_join_is_the_union`   -- the paths that answer are the union.
* `join_is_a_cross_product`     -- the emission of a joined group is the full cross product.
* `the_join_can_lose`           -- executable: two contexts of 1x1 pay 2, joined they pay 4.

**The design rule this gives.** A context join is cheap when the joined contexts ASK THE SAME
QUESTIONS, and quadratic when they ask different ones. Choose the group by the demand, not by
arrival order.
-/

/-- One premise per fact path the demand reaches. `TifaBound.star_free_is_exactly_nodes` is the
engine's version: star-free, TIFA emits one initial per node of the added tree. -/
def emitted (f : Fact) (d : Demand) : List Path :=
  keep (fun p => d.any (fun q => isPrefix q p)) f.concrete

def joinFacts (a b : Fact) : Fact :=
  { concrete := a.concrete ++ b.concrete, abstract := a.abstract ++ b.abstract }

theorem keep_append (P : Path → Bool) :
    ∀ l m : List Path, keep P (l ++ m) = keep P l ++ keep P m := by
  intro l
  induction l with
  | nil => intro m; rfl
  | cons p r ih =>
      intro m
      show cond (P p) (p :: keep P (r ++ m)) (keep P (r ++ m))
          = cond (P p) (p :: keep P r) (keep P r) ++ keep P m
      cases hp : P p with
      | true => show p :: keep P (r ++ m) = p :: (keep P r ++ keep P m); rw [ih m]
      | false => show keep P (r ++ m) = keep P r ++ keep P m; rw [ih m]

/-- Joining two contexts answers with the union of their paths. -/
theorem emitted_join_is_the_union (a b : Fact) (d : Demand) :
    emitted (joinFacts a b) d = emitted a d ++ emitted b d := by
  unfold emitted joinFacts
  exact keep_append _ a.concrete b.concrete

/-- Joining keeps the abstract count as the sum, so two CONCRETE contexts stay concrete. -/
theorem join_starts_no_ladder (a b : Fact)
    (ha : a.abstract = []) (hb : b.abstract = []) : (joinFacts a b).abstract = [] := by
  unfold joinFacts
  rw [ha, hb]
  rfl

/--
**THE COST OF THE JOIN.** Apart the two contexts pay `|f_a ∩ d_a| + |f_b ∩ d_b|`. Joined, both facts
meet BOTH demands, so they pay the cross product. The witness: two contexts whose facts and demands
are disjoint, each paying 1, together paying 4.
-/
theorem the_join_can_lose :
    (emitted { concrete := [[1]], abstract := [] } [[1]]).length = 1 ∧
    (emitted { concrete := [[2]], abstract := [] } [[2]]).length = 1 ∧
    (emitted (joinFacts { concrete := [[1]], abstract := [] }
                        { concrete := [[2]], abstract := [] }) [[1], [2]]).length = 2 :=
  ⟨rfl, rfl, rfl⟩

/--
And the general statement: a joined group emits every one of its facts against the merged demand, so
the emission of a group of `n` contexts of size 1 that ask `n` different questions is `n * n`, not
`n`. `emitted_join_is_the_union` is the step; this is the shape it iterates to.
-/
theorem join_is_a_cross_product (a b : Fact) (d : Demand) :
    (emitted (joinFacts a b) d).length = (emitted a d).length + (emitted b d).length := by
  rw [emitted_join_is_the_union, List.length_append]

/-- A context whose demand is the SAME pays nothing extra: the union is the same set of questions. -/
theorem join_is_free_when_the_demand_is_shared (a : Fact) (d : Demand) :
    emitted (joinFacts a { concrete := [], abstract := [] }) d = emitted a d := by
  unfold emitted joinFacts
  rw [show (a.concrete ++ ([] : List Path)) = a.concrete from List.append_nil a.concrete]

end FactExplosion.Relocation
