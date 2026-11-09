/-
# Bounding the context POPULATION

Every operator measured so far bounds the SHAPE of one fact: depth, width, the graph ladder, the
retroactive re-application, hash-consing. Measured on conductor, all of them leave the store at the
same size, because the store is

    (analyzer context) x (instruction) x (tree size)

and only the last factor is a shape. The first factor is the number of distinct initial facts a
method is analysed for, and it is what grows: 496,524 pairs over 8,313 methods, where 133 methods
(1.6%) hold 56.6% of them and one method holds 7,536.

This module specifies the missing operator. It caps the contexts per method and, at the cap, JOINS
the overflow instead of dropping it. Dropping is a false negative; joining is an over-approximation.
-/

namespace FactExplosion.ContextCap

/-- An access path. -/
abbrev Path := List Nat

/-- A fact, as the finite set of paths it answers. -/
abbrev Fact := List Path

/-- The store of initial facts a method is analysed for. -/
abbrev Store := List Fact

def accepts (f : Fact) (p : Path) : Bool := f.any (fun q => q == p)

/-- The join of two facts answers exactly what either answered. -/
def join (a b : Fact) : Fact := a ++ b

theorem join_accepts (a b : Fact) (p : Path) :
    accepts (join a b) p = (accepts a p || accepts b p) := by
  unfold accepts join
  rw [List.any_append]

/-- What the whole store answers. -/
def answers (s : Store) (p : Path) : Bool := s.any (fun f => accepts f p)

/-! ## The operator -/

/--
Add an initial fact under a cap.

Below the cap the fact is kept apart, which is full precision. At the cap it is JOINED into the
first context. The join is the engine's own `mergeAdd`, which is exact on the denotation
(`join_accepts`), so nothing the analysis could answer becomes unanswerable.
-/
def addCapped (K : Nat) (s : Store) (f : Fact) : Store :=
  if s.length < K then f :: s
  else match s with
       | [] => [f]
       | g :: rest => join g f :: rest

/-! ## No false negative, in either direction -/

/-- **Everything the store answered, the capped store still answers.** -/
theorem capped_keeps_the_store (K : Nat) (s : Store) (f : Fact) (p : Path)
    (h : answers s p = true) : answers (addCapped K s f) p = true := by
  simp only [answers] at h
  unfold addCapped
  split
  · simp only [answers, List.any_cons]
    rw [h]; simp
  · cases s with
    | nil => simp at h
    | cons g rest =>
        simp only [List.any_cons] at h
        simp only [answers, List.any_cons]
        rw [join_accepts]
        cases hg : accepts g p with
        | true => simp
        | false =>
            rw [hg] at h; simp at h
            simp [h]

/-- **And the fact just added is answered too.** -/
theorem capped_keeps_the_new_fact (K : Nat) (s : Store) (f : Fact) (p : Path)
    (h : accepts f p = true) : answers (addCapped K s f) p = true := by
  unfold addCapped
  split
  · simp only [answers, List.any_cons]; rw [h]; simp
  · cases s with
    | nil => simp [answers, h]
    | cons g rest =>
        simp only [answers, List.any_cons]
        rw [join_accepts, h]
        simp

/--
**No false negative is possible.** The capped store answers everything the uncapped store would
have answered, for every path, every cap and every history.
-/
theorem no_false_negative (K : Nat) (s : Store) (f : Fact) (p : Path)
    (h : answers (f :: s) p = true) : answers (addCapped K s f) p = true := by
  simp only [answers, List.any_cons] at h
  cases hf : accepts f p with
  | true => exact capped_keeps_the_new_fact K s f p hf
  | false =>
      rw [hf] at h; simp at h
      exact capped_keeps_the_store K s f p (by simp [answers, h])

/-! ## The population bound -/

/-- **The store never passes the cap.** -/
theorem addCapped_bounds (K : Nat) (hK : 0 < K) (s : Store) (f : Fact)
    (h : s.length ≤ K) : (addCapped K s f).length ≤ K := by
  unfold addCapped
  split
  · simp; omega
  · cases s with
    | nil => simp; omega
    | cons g rest => simp; omega

/-- Folding the whole arrival history keeps the bound, so the population is bounded per method. -/
theorem fold_bounds (K : Nat) (hK : 0 < K) :
    ∀ (fs : List Fact) (s : Store), s.length ≤ K →
      (fs.foldl (fun acc f => addCapped K acc f) s).length ≤ K := by
  intro fs
  induction fs with
  | nil => intro s h; exact h
  | cons f rest ih =>
      intro s h
      exact ih (addCapped K s f) (addCapped_bounds K hK s f h)

/-! ## The concept and the optimization

Uncapped, the store holds one context per distinct arrival. Capped, it holds at most `K`. The
measured conductor distribution makes the separation concrete: 133 methods hold 1000+ contexts each
and 56.6% of the whole population.
-/

/-- The uncapped store keeps every arrival apart. -/
def addPlain (s : Store) (f : Fact) : Store := f :: s

theorem plain_grows : ∀ (fs : List Fact) (s : Store),
    (fs.foldl addPlain s).length = fs.length + s.length := by
  intro fs
  induction fs with
  | nil => intro s; simp
  | cons f rest ih => intro s; simp [addPlain, ih]; omega

set_option maxRecDepth 10000 in
/-- One method with 7,536 arrivals -- conductor's worst -- against a cap of 100. -/
theorem the_separation :
    ((List.replicate 7536 ([[1]] : Fact)).foldl addPlain []).length = 7536 ∧
    ((List.replicate 7536 ([[1]] : Fact)).foldl (fun acc f => addCapped 100 acc f) []).length ≤ 100 := by
  constructor
  · rw [plain_grows, List.length_replicate]; rfl
  · exact fold_bounds 100 (by omega) _ [] (by simp)

/-! ## The trie, and the reader the design needs

The engine does not hold contexts in a list. `MethodEdgesInitialToFinalTreeApSet` keeps them in a
TRIE keyed by the initial access path (`AccessBasedStorage.getOrCreateNode`), and `null` is the
ROOT. So "join the overflow into one context" is realised as "store at an ancestor".

That makes the READER the load-bearing part, and this section is why. The shipped reader is

    val storage = sameInitialAccessEdges.find(initial)?.current ?: return

which reads the EXACT node only. Below, `readExact` models it and `readWithAncestors` models the
repair. The theorem `the_naive_reader_loses` is a false negative, exhibited constructively.
-/

/-- A trie node address: the accessor chain from the root. -/
abbrev Addr := List Nat

/-- A store: what each address holds. -/
abbrev Trie := List (Addr × Fact)

/-- `a` is a prefix of `b`, so `a` names an ancestor of `b`. -/
def isPrefix : Addr → Addr → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => Nat.beq x y && isPrefix xs ys

/-- `Nat.beq` is reflexive, proved by recursion so no instance lemma is needed. `beq_self_eq_true`
would do it but it carries `Classical.choice`, which this development does not admit. -/
theorem natBeqRefl : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => natBeqRefl n

/-- The shipped reader: the exact node, and nothing above it. -/
def readExact (t : Trie) (a : Addr) (p : Path) : Bool :=
  t.any (fun e => (e.1 == a) && accepts e.2 p)

/-- The repaired reader: every node on the root-to-node path. -/
def readWithAncestors (t : Trie) (a : Addr) (p : Path) : Bool :=
  t.any (fun e => isPrefix e.1 a && accepts e.2 p)

/-- Every address is a prefix of itself. -/
theorem isPrefix_refl : ∀ a : Addr, isPrefix a a = true := by
  intro a
  induction a with
  | nil => rfl
  | cons x xs ih =>
      show (Nat.beq x x && isPrefix xs xs) = true
      rw [ih, natBeqRefl x]
      rfl

/-- Storing at the exact address is answered by both readers. -/
theorem exact_is_read (t : Trie) (a : Addr) (p : Path) (f : Fact)
    (h : accepts f p = true) : readWithAncestors ((a, f) :: t) a p = true := by
  simp only [readWithAncestors, List.any_cons]
  rw [isPrefix_refl a, h]
  rfl

/--
**The naive reader turns the collapse into a false negative.** A fact stored at the root is not
answered at a deeper address. This is a counterexample, executable, and it is the bug the
implementation must not have.
-/
theorem the_naive_reader_loses :
    readExact [([], [[7]])] [3] [7] = false ∧
    readWithAncestors [([], [[7]])] [3] [7] = true := by decide

/--
**The repaired reader loses nothing, ever.** Whatever the exact node answered, the ancestor reader
answers too -- so replacing the reader can only ADD, and the collapse it enables is sound.
-/
theorem ancestors_reader_never_loses : ∀ (t : Trie) (a : Addr) (p : Path),
    readExact t a p = true → readWithAncestors t a p = true := by
  intro t
  induction t with
  | nil => intro a p h; exact absurd h (by simp [readExact])
  | cons e rest ih =>
      intro a p h
      simp only [readExact, List.any_cons] at h
      simp only [readWithAncestors, List.any_cons]
      cases hc : (e.1 == a && accepts e.2 p) with
      | true =>
          have hpair := (Bool.and_eq_true _ _).mp hc
          have h1 : e.1 = a := beq_iff_eq.mp hpair.1
          have hpre : isPrefix e.1 a = true := by rw [h1]; exact isPrefix_refl a
          rw [hpre, hpair.2]
          rfl
      | false =>
          rw [hc] at h
          simp only [Bool.false_or] at h
          have hrest := ih a p h
          simp only [readWithAncestors] at hrest
          rw [hrest]
          exact Bool.or_true _

/-! ## The fast path

The ancestor reader is only NEEDED once something is actually joined above the queried node. The
implementation keeps a `joinedAbove` flag and uses the cheap exact reader until the first join. This
is the theorem that makes that sound, and it matters for speed: conductor at cap 1000 joined 1,053
arrivals out of ~500,000 contexts, so without the flag nearly every query paid the ancestor walk for
nothing.
-/

/-- No entry sits at a PROPER ancestor of `a`. -/
def noProperAncestor (t : Trie) (a : Addr) : Bool :=
  t.all (fun e => !(isPrefix e.1 a) || e.1 == a)

/-- **While nothing is joined above, the exact reader is already complete.** -/
theorem fast_path_is_complete : ∀ (t : Trie) (a : Addr) (p : Path),
    noProperAncestor t a = true → readWithAncestors t a p = readExact t a p := by
  intro t
  induction t with
  | nil => intro a p _; rfl
  | cons e rest ih =>
      intro a p h
      simp only [noProperAncestor, List.all_cons, Bool.and_eq_true] at h
      have hhead := h.1
      have htail : noProperAncestor rest a = true := h.2
      have hh : isPrefix e.1 a = (e.1 == a) := by
        cases hb : (e.1 == a) with
        | true =>
            have heq : e.1 = a := beq_iff_eq.mp hb
            rw [heq, isPrefix_refl]
        | false =>
            cases hp : isPrefix e.1 a with
            | true => rw [hp, hb] at hhead; exact absurd hhead (by decide)
            | false => rfl
      have htails := ih a p htail
      simp only [readWithAncestors, readExact, List.any_cons] at htails ⊢
      rw [hh, htails]

end FactExplosion.ContextCap
