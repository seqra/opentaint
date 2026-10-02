import MarkScan

/-!
# Oracle generator for the Kotlin mark-set core (spec §8, Layer 1)

`lake exe markset-oracle <count> <seed>` prints one JSON document with `count`
seeded random programs and, for each, the answers of the proven reference
functions `refInS`, `refApplicable` and `refNeeded` (`Algorithm.lean`).

This file is outside `MarkScan/`, so it is not part of the audited library:
it only generates test data. The expected answers are computed exclusively by
the reference functions; every generated program is checked against
`Algorithm.WF` (a Bool check over the finite program tables) before use, which
is the hypothesis of `refInS_iff`, `refApplicable_iff` and `refNeeded_iff`.

Program shape: `method := id`, no kills, a straight-line CFG `0 → 1 → … → k-1`
per node with exit `k-1`, identity base maps, no copies. Assigns use base 0.
-/

open MarkScan MarkScan.Algorithm

namespace Oracle

/-! ## Deterministic LCG -/

abbrev Gen := StateM Nat

def next : Gen Nat := do
  let s ← get
  let s' := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
  set s'
  return s' / 8589934592

/-- Uniform in `[0, n)` (`0` when `n = 0`). -/
def below (n : Nat) : Gen Nat := do
  if n == 0 then return 0 else return (← next) % n

/-- Uniform in `[lo, hi]`. -/
def between (lo hi : Nat) : Gen Nat := do
  return lo + (← below (hi - lo + 1))

def chance (pct : Nat) : Gen Bool := do
  return (← below 100) < pct

def pick {α : Type} [Inhabited α] (l : List α) : Gen α := do
  return l.getD (← below l.length) default

def repeatGen {α : Type} (n : Nat) (g : Gen α) : Gen (List α) := do
  let mut acc := []
  for _ in [0:n] do
    acc := (← g) :: acc
  return acc.reverse

/-! ## Raw programs (finite tables) -/

def numMarks : Nat := 5
def numBases : Nat := 3

structure Raw where
  nodeCount : Nat
  roots : List Node
  npcs : List Nat
  calls : List (Node × Pc × Node)
  sites : List (Node × Pc × ESite)
  cleaner : List (Node × Pc × Mark)

def Raw.pcCount (r : Raw) (n : Node) : Nat := r.npcs.getD n 0

def Raw.toProgram (r : Raw) : Program where
  nodes := List.range r.nodeCount
  roots := r.roots
  pcs := fun n => List.range (r.pcCount n)
  succ := fun n pc => if pc + 1 < r.pcCount n then [pc + 1] else []
  exits := fun n => if r.pcCount n = 0 then [] else [r.pcCount n - 1]
  sites := fun n pc => (r.sites.filter fun e => e.1 == n && e.2.1 == pc).map (·.2.2)
  calls := fun n pc => (r.calls.filter fun e => e.1 == n && e.2.1 == pc).map (·.2.2)
  mapIn := fun _ _ b => some b
  mapOut := fun _ _ b => some b
  kills := fun _ _ _ => false
  method := id
  cleanerAtoms := fun n pc => (r.cleaner.filter fun e => e.1 == n && e.2.1 == pc).map (·.2.2)

/-- Decidable `Algorithm.WF` for programs built by `Raw.toProgram`. `sites`,
`calls` and `cleanerAtoms` of the program are non-empty only at the `(n, pc)`
entries of the raw tables, so checking those entries covers the universally
quantified clauses. Also checks that every node has pc `0` and that every call
sits at a listed statement of a listed node. -/
def wfb (r : Raw) : Bool :=
  let p := r.toProgram
  let listed (n pc : Nat) : Bool := p.nodes.contains n && (p.pcs n).contains pc
  (p.roots.all fun x => p.nodes.contains x) &&
  (p.nodes.all fun n => (p.callees n).all fun c => p.nodes.contains c) &&
  (p.nodes.all fun n => (p.pcs n).contains 0) &&
  (r.sites.all fun e => listed e.1 e.2.1) &&
  (r.calls.all fun e => listed e.1 e.2.1 && p.nodes.contains e.2.2) &&
  (r.cleaner.all fun e => listed e.1 e.2.1) &&
  r.npcs.length == r.nodeCount

/-! ## Random generation -/

def genLit : Gen ELit := do
  let b ← below numBases
  let m ← below numMarks
  let neg ← chance 15
  return ⟨⟨b, m⟩, neg⟩

def otherBase (b : Base) : Gen Base := do
  return (b + 1 + (← below (numBases - 1))) % numBases

def genCube : Gen ECube := do
  let r ← below 100
  if r < 12 then
    return []                                   -- constant-true cube
  else if r < 30 then                           -- joined: two marks, different bases
    let b1 ← below numBases
    let b2 ← otherBase b1
    let m1 ← below numMarks
    let m2 ← below numMarks
    return [⟨⟨b1, m1⟩, false⟩, ⟨⟨b2, m2⟩, false⟩]
  else if r < 40 then                           -- joined: same mark, different bases
    let b1 ← below numBases
    let b2 ← otherBase b1
    let m ← below numMarks
    return [⟨⟨b1, m⟩, false⟩, ⟨⟨b2, m⟩, false⟩]
  else
    let k ← pick [1, 1, 1, 1, 2, 3]
    repeatGen k genLit

def genCond : Gen ECond := do
  if ← chance 7 then return []                  -- constant false
  let k ← pick [1, 1, 1, 2, 2, 3]
  repeatGen k genCube

def genGens (lo hi : Nat) : Gen (List Fact) := do
  let k ← between lo hi
  repeatGen k (do return ⟨0, ← below numMarks⟩)

def genSite (rule : RuleId) : Gen ESite := do
  let r ← below 100
  if r < 35 then
    let cond ← if ← chance 60 then pure [[]] else genCond
    return { rule, kind := .source, cond, assigns := ← genGens 1 2, copies := [] }
  else if r < 65 then
    let cond ← genCond
    let gens ← if ← chance 50 then pure [] else genGens 1 2
    return { rule, kind := .sink, cond, assigns := gens, copies := [] }
  else
    let cond ← genCond
    return { rule, kind := .passThrough, cond, assigns := ← genGens 0 2, copies := [] }

/-- Distinct sample of `k` elements of `[0, n)`. -/
def sample (n k : Nat) : Gen (List Nat) := do
  let mut pool := List.range n
  let mut out := []
  for _ in [0:k] do
    if pool.isEmpty then break
    let x ← pick pool
    pool := pool.erase x
    out := out ++ [x]
  return out

def reachable (roots : List Node) (calls : List (Node × Pc × Node)) (fuel : Nat) : List Node :=
  go fuel roots
where
  go : Nat → List Node → List Node
    | 0, r => r
    | f + 1, r =>
      let nxt := (calls.filter fun e => r.contains e.1).map (·.2.2)
      let new := (nxt.filter fun x => !r.contains x).eraseDups
      if new.isEmpty then r else go f (r ++ new)

def genRaw : Gen Raw := do
  let nc ← between 1 6
  let npcs ← repeatGen nc (between 1 4)
  let nr ← between 1 (min 3 nc)
  let roots ← sample nc nr
  let pcOf (n : Node) : Gen Pc := below (npcs.getD n 1)
  -- calls: each statement calls a random node with some probability; self and
  -- back edges give recursion and cycles
  let mut calls : List (Node × Pc × Node) := []
  for n in List.range nc do
    for pc in List.range (npcs.getD n 1) do
      if ← chance 30 then
        calls := calls ++ [(n, pc, ← below nc)]
  if ← chance 80 then
    -- connect every node to some root
    for _ in [0:nc] do
      let reach := reachable roots calls nc
      let miss := (List.range nc).filter fun x => !reach.contains x
      if miss.isEmpty then break
      let u ← pick miss
      let src ← pick reach
      calls := calls ++ [(src, ← pcOf src, u)]
  else
    -- cut every edge into one non-root node, so it is unreachable
    let nonRoots := (List.range nc).filter fun x => !roots.contains x
    if !nonRoots.isEmpty then
      let v ← pick nonRoots
      calls := calls.filter fun e => e.2.2 != v
  let mut sites : List (Node × Pc × ESite) := []
  let mut rule := 0
  for n in List.range nc do
    let k ← between 0 3
    for _ in [0:k] do
      let pc ← pcOf n
      sites := sites ++ [(n, pc, ← genSite rule)]
      rule := rule + 1
  let mut cleaner : List (Node × Pc × Mark) := []
  for n in List.range nc do
    if ← chance 12 then
      cleaner := cleaner ++ [(n, ← pcOf n, ← below numMarks)]
  return { nodeCount := nc, roots, npcs, calls, sites, cleaner }

/-- Generate a WF program; regenerate from the advanced state otherwise. -/
def genWF : Nat → Gen (Option Raw)
  | 0 => return none
  | f + 1 => do
    let r ← genRaw
    if wfb r then return some r else genWF f

/-! ## Tabulated evaluation of the reference functions

`refIter` iterates on functions `Node → List Mark`. Compiled, the state after
`k` rounds is a closure that re-evaluates round `k - 1` at every lookup, so the
cost is exponential in the number of rounds. The loop below runs the same
round (`refRound`) and the same stop test (`refStable`) on a table of the root
entries instead, and the theorems `memoInS_eq`, `memoApplicable_eq` and
`memoNeeded_eq` prove that the answers equal `refInS`, `refApplicable` and
`refNeeded` on every program (no WF needed): the reference functions only ever
read the state at roots. -/

/-- A table of root entries, read as a state. -/
def look (t : List (Node × List Mark)) (E : Node) : List Mark := (t.lookup E).getD []

def memoStep (p : Program) (t : List (Node × List Mark)) : List (Node × List Mark) :=
  p.roots.map fun E => (E, refRound p (look t) E)

def memoFinal (p : Program) : Node → List Mark :=
  look (AlgorithmLemmas.iterC (memoStep p) (fun t => refStable p (look t)) (refFuel p)
    (p.roots.map fun E => (E, []))).1

def memoInS (p : Program) (E : Node) (m : Mark) : Bool :=
  decide (m ∈ ((p.roots.map fun E => (E, memoFinal p E)).lookup E).getD [])

def memoApplicable (p : Program) (n : Node) (pc : Pc) (σ : ESite) : Bool :=
  applicableOn p (memoFinal p) n pc σ

def memoNeeded (p : Program) (m : Mark) : Bool :=
  decide (m ∈ neededSet (appSites p (memoApplicable p)) (cleanerSeeds p))

section Proofs

/-- Two states agree on the roots. -/
def Agree (p : Program) (S T : Node → List Mark) : Prop := ∀ E, E ∈ p.roots → S E = T E

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} :
    ∀ l : List α, (∀ x, x ∈ l → f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: t, h => by
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self), flatMap_congr_mem t (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem any_congr_mem {α : Type} {f g : α → Bool} :
    ∀ l : List α, (∀ x, x ∈ l → f x = g x) → l.any f = l.any g
  | [], _ => rfl
  | a :: t, h => by
    simp only [List.any_cons]
    rw [h a (List.mem_cons_self), any_congr_mem t (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem all_congr_mem {α : Type} {f g : α → Bool} :
    ∀ l : List α, (∀ x, x ∈ l → f x = g x) → l.all f = l.all g
  | [], _ => rfl
  | a :: t, h => by
    simp only [List.all_cons]
    rw [h a (List.mem_cons_self), all_congr_mem t (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem refUM_congr {p : Program} {S T : Node → List Mark} (h : Agree p S T) :
    refUM p S = refUM p T := by
  funext k
  unfold refUM
  exact flatMap_congr_mem _ fun q hq => by
    rw [h q.1 (AlgorithmLemmas.mem_rootPairs.mp hq).1]

theorem refGens_congr {p : Program} {S T : Node → List Mark} (h : Agree p S T)
    {E : Node} (hE : E ∈ p.roots) : refGens p S E = refGens p T E := by
  have hc : refCubeOk p S E = refCubeOk p T E := by
    funext k c
    simp only [refCubeOk, refUM_congr h, h E hE]
  unfold refGens refSiteOk
  rw [hc, refUM_congr h]

theorem refRound_congr {p : Program} {S T : Node → List Mark} (h : Agree p S T) :
    Agree p (refRound p S) (refRound p T) := fun E hE => by
  simp only [refRound, refGens_congr h hE, h E hE]

theorem refStable_congr {p : Program} {S T : Node → List Mark} (h : Agree p S T) :
    refStable p S = refStable p T := by
  unfold refStable
  exact all_congr_mem _ fun E hE => by rw [refGens_congr h hE, h E hE]

theorem look_map (p : Program) (F : Node → List Mark) :
    Agree p F (look (p.roots.map fun E => (E, F E))) := fun E hE => by
  simp only [look, AlgorithmLemmas.lookup_map_self F p.roots E hE, Option.getD_some]

theorem memoFinal_agree (p : Program) : Agree p (refFinal p) (memoFinal p) := by
  have hstep : ∀ S t, Agree p S (look t) → Agree p (refRound p S) (look (memoStep p t)) :=
    fun S t h E hE => by
      rw [refRound_congr h E hE]
      exact look_map p (refRound p (look t)) E hE
  have init : Agree p (fun _ => []) (look (p.roots.map fun E => (E, []))) :=
    look_map p (fun _ => [])
  exact (AlgorithmLemmas.iterC_lockstep (refRound p) (memoStep p) (refStable p)
    (fun t => refStable p (look t)) (fun S t => Agree p S (look t))
    (fun S t h => refStable_congr h) hstep (refFuel p) _ _ init).1

theorem memoInS_eq (p : Program) (E : Node) (m : Mark) : memoInS p E m = refInS p E m := by
  have : refSets p = p.roots.map fun E => (E, memoFinal p E) :=
    List.map_congr_left fun E hE => by rw [memoFinal_agree p E hE]
  simp only [memoInS, refInS, this]

theorem memoApplicable_fun (p : Program) : memoApplicable p = refApplicable p := by
  funext n pc σ
  have h := memoFinal_agree p
  simp only [memoApplicable, refApplicable, applicableOn]
  congr 1
  refine any_congr_mem _ fun c _ => ?_
  simp only [refCubeSat, refUM_congr h]
  split
  · exact any_congr_mem _ fun E hE => by rw [h E hE]
  · rfl

theorem memoApplicable_eq (p : Program) (n : Node) (pc : Pc) (σ : ESite) :
    memoApplicable p n pc σ = refApplicable p n pc σ := by
  rw [memoApplicable_fun]

theorem memoNeeded_eq (p : Program) (m : Mark) : memoNeeded p m = refNeeded p m := by
  simp only [memoNeeded, refNeeded, memoApplicable_fun]

end Proofs

/-! ## Expected answers (reference functions, via the tabulated loop) -/

structure Expected where
  inS : List (Node × Mark)
  applicable : List Nat
  needed : List Mark

def Raw.marksUsed (r : Raw) : List Mark :=
  r.sites.flatMap (fun e => (e.2.2.cond.flatMap fun c => c.map (·.fact.mark)) ++
    e.2.2.assigns.map (·.mark)) ++ r.cleaner.map (·.2.2)

def expected (r : Raw) : Expected :=
  let p := r.toProgram
  let bound := (r.marksUsed.foldl max 0 |>.max (numMarks - 1)) + 2
  let marks := List.range bound
  { inS := r.roots.flatMap fun E => (marks.filter fun m => memoInS p E m).map fun m => (E, m)
    applicable := ((List.range r.sites.length).zip r.sites).filterMap fun (i, n, pc, σ) =>
      if memoApplicable p n pc σ then some i else none
    needed := marks.filter fun m => memoNeeded p m }

/-! ## JSON -/

def jNat (n : Nat) : String := toString n
def jBool (b : Bool) : String := if b then "true" else "false"
def jArr (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"
def jStr (s : String) : String := "\"" ++ s ++ "\""
def jObj (kvs : List (String × String)) : String :=
  "{" ++ ",".intercalate (kvs.map fun (k, v) => jStr k ++ ":" ++ v) ++ "}"

def jKind : Kind → String
  | .source => jStr "source"
  | .sink => jStr "sink"
  | .passThrough => jStr "passThrough"

def jSite (e : Node × Pc × ESite) : String :=
  let (n, pc, σ) := e
  jObj [("node", jNat n), ("pc", jNat pc), ("kind", jKind σ.kind),
    ("cond", jArr (σ.cond.map fun c => jArr (c.map fun l =>
      jArr [jNat l.fact.base, jNat l.fact.mark, jBool l.negated]))),
    ("gens", jArr (σ.assigns.map fun a => jNat a.mark))]

def jProgram (seed : Nat) (r : Raw) (x : Expected) : String :=
  jObj [("seed", jNat seed), ("nodeCount", jNat r.nodeCount),
    ("roots", jArr (r.roots.map jNat)),
    ("calls", jArr (r.calls.map fun (a, pc, b) => jArr [jNat a, jNat pc, jNat b])),
    ("pcs", jArr ((List.range r.nodeCount).flatMap fun n =>
      (List.range (r.pcCount n)).map fun pc => jArr [jNat n, jNat pc])),
    ("sites", jArr (r.sites.map jSite)),
    ("cleanerAtoms", jArr (r.cleaner.map fun (n, pc, m) => jArr [jNat n, jNat pc, jNat m])),
    ("expected", jObj [
      ("inS", jArr (x.inS.map fun (E, m) => jArr [jNat E, jNat m])),
      ("applicable", jArr (x.applicable.map jNat)),
      ("needed", jArr (x.needed.map jNat))])]

/-! ## Statistics (stderr) -/

def hasJoined (r : Raw) : Bool :=
  r.sites.any fun e => e.2.2.abstract.cond.any fun c => 2 ≤ c.length

def hasUnreachable (r : Raw) : Bool :=
  (reachable r.roots r.calls r.nodeCount).length < r.nodeCount

end Oracle

open Oracle in
def main (args : List String) : IO UInt32 := do
  let (count, seed) ← match args with
    | [c, s] => match c.toNat?, s.toNat? with
      | some c, some s => pure (c, s)
      | _, _ => do IO.eprintln "usage: markset-oracle <count> <seed>"; return 2
    | _ => do IO.eprintln "usage: markset-oracle <count> <seed>"; return 2
  let out ← IO.getStdout
  out.putStr "{\"programs\":["
  let mut first := true
  let mut nJoined := 0
  let mut nApp := 0
  let mut nNeeded := 0
  let mut nUnreach := 0
  let mut nInS := 0
  for i in [0:count] do
    let s := seed + i
    -- mix the small seed before use
    let (r?, _) := (do let _ ← next; let _ ← next; genWF 100 : Gen _).run s
    match r? with
    | none => IO.eprintln s!"seed {s}: no WF program after 100 attempts"; return 1
    | some r =>
      let x := expected r
      unless first do out.putStr ","
      first := false
      out.putStr (jProgram s r x)
      if hasJoined r then nJoined := nJoined + 1
      if !x.applicable.isEmpty then nApp := nApp + 1
      if !x.needed.isEmpty then nNeeded := nNeeded + 1
      if !x.inS.isEmpty then nInS := nInS + 1
      if hasUnreachable r then nUnreach := nUnreach + 1
  out.putStrLn "]}"
  IO.eprintln s!"programs={count} joinedCubes={nJoined} nonEmptyInS={nInS} nonEmptyApplicable={nApp} nonEmptyNeeded={nNeeded} unreachableNodes={nUnreach}"
  return 0
