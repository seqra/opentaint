/-
  Counted depth metadata for the implementation trie. Payloads and accessor
  identities do not affect depth. extend represents one child accessor; merge
  represents sibling branches. false represents an uncounted class accessor.

  The computed deepest path witnesses the cached maximum. The skip guard is
  equivalent to checking every stored path. This proves the metadata shortcut,
  not the full field-limit tree operation or an unbounded JVM heap model.
  JVM Int storage additionally requires the counted depth to fit in a signed
  Int; the constructor checks addition instead of silently saturating it.
-/
import ApSpec.Basic

namespace ApSpec.CurrentDepthCache

inductive DepthTree where
  | leaf
  | extend (counted : Bool) (child : DepthTree)
  | merge (left right : DepthTree)
deriving Repr

def counted (a : Bool) : Nat := if a then 1 else 0

def countedLength : List Bool → Nat
  | [] => 0
  | a :: p => counted a + countedLength p

def paths : DepthTree → List (List Bool)
  | .leaf => [[]]
  | .extend a t => (paths t).map (a :: ·)
  | .merge a b => paths a ++ paths b

def cachedDepth : DepthTree → Nat
  | .leaf => 0
  | .extend a t => counted a + cachedDepth t
  | .merge a b => max (cachedDepth a) (cachedDepth b)

def deepestPath : DepthTree → List Bool
  | .leaf => []
  | .extend a t => a :: deepestPath t
  | .merge a b =>
      if cachedDepth b ≤ cachedDepth a then deepestPath a else deepestPath b

theorem path_le_cache (t : DepthTree) (p : List Bool) (h : p ∈ paths t) :
    countedLength p ≤ cachedDepth t := by
  induction t generalizing p with
  | leaf =>
      have hp : p = [] := by simpa [paths] using h
      subst p
      exact Nat.le_refl 0
  | extend a t ih =>
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
      simpa [countedLength, cachedDepth] using Nat.add_le_add_left (ih q hq) (counted a)
  | merge a b iha ihb =>
      rcases List.mem_append.mp h with ha | hb
      · exact Nat.le_trans (iha p ha) (Nat.le_max_left _ _)
      · exact Nat.le_trans (ihb p hb) (Nat.le_max_right _ _)

theorem deepest_mem (t : DepthTree) : deepestPath t ∈ paths t := by
  induction t with
  | leaf => simp [deepestPath, paths]
  | extend a t ih => exact List.mem_map.mpr ⟨deepestPath t, ih, rfl⟩
  | merge a b iha ihb =>
      simp only [deepestPath, paths]
      split
      · exact List.mem_append.mpr (Or.inl iha)
      · exact List.mem_append.mpr (Or.inr ihb)

theorem deepest_count (t : DepthTree) : countedLength (deepestPath t) = cachedDepth t := by
  induction t with
  | leaf => rfl
  | extend a t ih => simp [deepestPath, countedLength, cachedDepth, ih]
  | merge a b iha ihb =>
      simp only [deepestPath, cachedDepth]
      split <;> rename_i h
      · rw [iha, Nat.max_eq_left h]
      · rw [ihb, Nat.max_eq_right (by omega)]

def skipB (t : DepthTree) (budget : Nat) : Bool := cachedDepth t ≤ budget

def Fits (t : DepthTree) (budget : Nat) : Prop :=
  ∀ p, p ∈ paths t → countedLength p ≤ budget

theorem skip_iff_fits (t : DepthTree) (budget : Nat) :
    skipB t budget = true ↔ Fits t budget := by
  simp only [skipB, decide_eq_true_eq]
  constructor
  · intro h p hp
    exact Nat.le_trans (path_le_cache t p hp) h
  · intro h
    simpa [deepest_count] using h (deepestPath t) (deepest_mem t)

/-- An executable witness attaining the exact maximum; no existential choice. -/
def depthWitness (t : DepthTree) :
    {p : List Bool // p ∈ paths t ∧ countedLength p = cachedDepth t} :=
  ⟨deepestPath t, deepest_mem t, deepest_count t⟩

def chain : Nat → DepthTree
  | 0 => .leaf
  | n + 1 => .extend true (chain n)

theorem chain_depth (n : Nat) : cachedDepth (chain n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chain, cachedDepth, counted, ih, Nat.add_comm]

def shortCap : Nat := 32767
def oldShortDepth (t : DepthTree) : Nat := min shortCap (cachedDepth t)
def oldSkipB (t : DepthTree) (budget : Nat) : Bool := oldShortDepth t ≤ budget

/-- This is also the former constructor's recursive saturation rule. -/
theorem old_extend_rule (a : Bool) (t : DepthTree) :
    oldShortDepth (.extend a t) = min shortCap (counted a + oldShortDepth t) := by
  cases a <;> simp only [oldShortDepth, cachedDepth, counted, Bool.false_eq_true,
    ↓reduceIte] <;> unfold shortCap <;> omega

theorem old_merge_rule (a b : DepthTree) :
    oldShortDepth (.merge a b) = max (oldShortDepth a) (oldShortDepth b) := by
  simp only [oldShortDepth, cachedDepth]
  omega

def jvmIntMax : Nat := 2147483647
def FitsInt (t : DepthTree) : Prop := cachedDepth t ≤ jvmIntMax

/-- Exact storage in a nonnegative signed Int; construction requires the bound. -/
def storedDepth (t : DepthTree) (h : FitsInt t) : {n : Nat // n ≤ jvmIntMax} :=
  ⟨cachedDepth t, h⟩

theorem stored_skip_iff_fits (t : DepthTree) (h : FitsInt t) (budget : Nat) :
    decide ((storedDepth t h).val ≤ budget) = true ↔ Fits t budget :=
  skip_iff_fits t budget

/-- The constructor's checked increment succeeds under the representability guard. -/
theorem child_increment_fits (a : Bool) (t : DepthTree) (h : FitsInt (.extend a t)) :
    counted a + cachedDepth t ≤ jvmIntMax := h

theorem short_cache_skips_over_limit : oldSkipB (chain 32768) 32767 = true := by
  simp [oldSkipB, oldShortDepth, shortCap, chain_depth]

theorem exact_cache_requires_cut : skipB (chain 32768) 32767 = false := by
  simp [skipB, chain_depth]

theorem over_limit_path : ¬ Fits (chain 32768) 32767 := by
  intro h
  have hn := (skip_iff_fits (chain 32768) 32767).mpr h
  rw [exact_cache_requires_cut] at hn
  cases hn

/-- A small runtime fixture includes sibling branches and an uncounted class accessor. -/
def fixture : DepthTree :=
  .merge (.extend false (.extend true .leaf)) (chain 3)

def workWitness : Bool :=
  cachedDepth fixture == 3 &&
  countedLength (depthWitness fixture).val == 3 &&
  skipB fixture 3 && !skipB fixture 2 &&
  oldSkipB (chain 32768) 32767 && !skipB (chain 32768) 32767

end ApSpec.CurrentDepthCache
