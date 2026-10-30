import Std

/-!
A constructive finite model for first-relevant CFG routing and producer-keyed
post-statement admission. It models routing and relation identity, not the AP
algebra or JVM rule semantics. The implementation must separately establish the
base-neutrality certificate described in the accompanying proposal.
-/
namespace CachedCfgDelivery

structure Graph (n : Nat) where
  next : Fin n → List (Fin n)
  relevant : Fin n → Bool

/-- An executable path. Every vertex from which it advances is neutral. -/
inductive Prefix {n : Nat} (g : Graph n) (start : Fin n) : Fin n → Type
  | root : Prefix g start start
  | step {a b : Fin n} (before : Prefix g start a)
      (neutral : g.relevant a = false) (edge : b ∈ g.next a) : Prefix g start b

def Prefix.nodes {n : Nat} {g : Graph n} {start target : Fin n} :
    Prefix g start target → List (Fin n)
  | .root => [start]
  | .step before _ _ => before.nodes ++ [target]

/-- A frontier target carries an executable stopped-path witness. -/
structure Target {n : Nat} (g : Graph n) (start : Fin n) where
  node : Fin n
  path : Prefix g start node
  stop : g.relevant node = true

private structure Open {n : Nat} (g : Graph n) (start : Fin n)
    (remaining done todo : List (Fin n)) where
  covers : ∀ v, v ∈ remaining ∨ v ∈ done
  root : start ∈ done ∨ start ∈ todo
  donePath : ∀ v, v ∈ done → Prefix g start v
  todoPath : ∀ v, v ∈ todo → Prefix g start v
  closed : ∀ v, v ∈ done → g.relevant v = false →
    ∀ w, w ∈ g.next v → w ∈ done ∨ w ∈ todo

/-- The visited set is closed under neutral steps. It has no queue left. -/
structure Closed {n : Nat} (g : Graph n) (start : Fin n) where
  visited : List (Fin n)
  root : start ∈ visited
  path : ∀ v, v ∈ visited → Prefix g start v
  closed : ∀ v, v ∈ visited → g.relevant v = false →
    ∀ w, w ∈ g.next v → w ∈ visited

private def remove (remaining : List (Fin n)) (q : Fin n) : List (Fin n) :=
  remaining.filter fun v => v != q

private theorem mem_remove_of_ne {remaining : List (Fin n)} {v q : Fin n}
    (different : v ≠ q) : v ∈ remove remaining q ↔ v ∈ remaining := by
  simp [remove, different]

private theorem remove_shorter {remaining : List (Fin n)} {q : Fin n}
    (mem : q ∈ remaining) : (remove remaining q).length < remaining.length := by
  induction remaining with
  | nil => simp at mem
  | cons a rest ih =>
    by_cases same : a = q
    · subst a
      have le := List.length_filter_le (p := fun v : Fin n => v != q) (l := rest)
      simp [remove] at *
      omega
    · have inRest : q ∈ rest := by simpa [same, Ne.symm same] using mem
      have shorter := ih inRest
      simp [remove, same] at *
      omega

private def advance {n : Nat} {g : Graph n} {start q : Fin n}
    {remaining done qs : List (Fin n)}
    (old : Open g start remaining done (q :: qs))
    (_pending : q ∈ remaining) :
    Open g start (remove remaining q) (q :: done)
      (qs ++ if g.relevant q then [] else g.next q) where
  covers := by
    intro v
    by_cases h : v = q
    · subst v; exact Or.inr (by simp)
    · rcases old.covers v with hv | hv
      · exact Or.inl ((mem_remove_of_ne h).mpr hv)
      · exact Or.inr (by simp [hv])
  root := by
    rcases old.root with h | h
    · exact Or.inl (by simp [h])
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (List.mem_append_left _ h)
  donePath := by
    intro v h
    by_cases same : v = q
    · subst v; exact old.todoPath q (by simp)
    · exact old.donePath v (by simpa [same] using h)
  todoPath := by
    intro v h
    by_cases hq : v ∈ qs
    · exact old.todoPath v (by simp [hq])
    · have new : v ∈ (if g.relevant q then [] else g.next q) :=
        (List.mem_append.mp h).resolve_left hq
      have neutral : g.relevant q = false := by
        cases hr : g.relevant q <;> simp_all
      have edge : v ∈ g.next q := by simpa [neutral] using new
      exact .step (old.todoPath q (by simp)) neutral edge
  closed := by
    intro v hv neutral w edge
    by_cases same : v = q
    · subst v
      exact Or.inr (by simp [neutral, edge])
    · have prev : v ∈ done := by simpa [same] using hv
      rcases old.closed v prev neutral w edge with hd | ht
      · exact Or.inl (by simp [hd])
      · rcases List.mem_cons.mp ht with heq | hqs
        · exact Or.inl (by simp [heq])
        · exact Or.inr (List.mem_append_left _ hqs)

private def dropSeen {n : Nat} {g : Graph n} {start q : Fin n}
    {remaining done qs : List (Fin n)}
    (old : Open g start remaining done (q :: qs))
    (absent : q ∉ remaining) : Open g start remaining done qs where
  covers := old.covers
  root := by
    have seen : q ∈ done := (old.covers q).resolve_left absent
    rcases old.root with h | h
    · exact Or.inl h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl (by simpa [h] using seen)
      · exact Or.inr h
  donePath := old.donePath
  todoPath := by
    intro v h; exact old.todoPath v (by simp [h])
  closed := by
    intro v hv neutral w edge
    have seen : q ∈ done := (old.covers q).resolve_left absent
    rcases old.closed v hv neutral w edge with hd | ht
    · exact Or.inl hd
    · rcases List.mem_cons.mp ht with h | h
      · exact Or.inl (by simpa [h] using seen)
      · exact Or.inr h

/-- FIFO graph search with a global visited set. A vertex is expanded once. -/
private def bfs {n : Nat} (g : Graph n) (start : Fin n)
    (remaining done todo : List (Fin n))
    (valid : Open g start remaining done todo) : Closed g start :=
  match todo with
  | [] => {
      visited := done
      root := valid.root.resolve_right (by simp)
      path := valid.donePath
      closed := by
        intro v hv neutral w edge
        exact (valid.closed v hv neutral w edge).resolve_right (by simp)
    }
  | q :: qs =>
    if h : q ∈ remaining then
      bfs g start (remove remaining q) (q :: done)
        (qs ++ if g.relevant q then [] else g.next q) (advance valid h)
    else bfs g start remaining done qs (dropSeen valid h)
termination_by (remaining.length, todo.length)
decreasing_by
  · apply Prod.Lex.left
    exact remove_shorter h
  · apply Prod.Lex.right
    simp

/-- The data-only projection is also executable without proof-carrying arguments. -/
private def visits {n : Nat} (g : Graph n)
    (remaining done todo : List (Fin n)) : List (Fin n) :=
  match todo with
  | [] => done
  | q :: qs =>
    if _h : q ∈ remaining then
      visits g (remove remaining q) (q :: done)
        (qs ++ if g.relevant q then [] else g.next q)
    else visits g remaining done qs
termination_by (remaining.length, todo.length)
decreasing_by
  · apply Prod.Lex.left; exact remove_shorter _h
  · apply Prod.Lex.right; simp

private theorem bfs_visits {n : Nat} (g : Graph n) (start : Fin n)
    (remaining done todo : List (Fin n))
    (valid : Open g start remaining done todo) :
    (bfs g start remaining done todo valid).visited = visits g remaining done todo := by
  cases todo with
  | nil => rw [bfs, visits]
  | cons q qs =>
    rw [bfs, visits]
    split
    · exact bfs_visits g start _ _ _ (advance valid _)
    · exact bfs_visits g start _ _ _ (dropSeen valid _)
termination_by (remaining.length, todo.length)
decreasing_by
  all_goals first
    | apply Prod.Lex.left; apply remove_shorter; assumption
    | apply Prod.Lex.right; subst_vars; simp

/-- A total finite search. No timeout fuel or unproved closure certificate. -/
def search {n : Nat} (g : Graph n) (start : Fin n) : Closed g start :=
  bfs g start (List.finRange n) [] [start] {
    covers := fun v => Or.inl (List.mem_finRange v)
    root := Or.inr (by simp)
    donePath := by intro v h; simp at h
    todoPath := by
      intro v h
      have same : v = start := by simpa using h
      subst v; exact .root
    closed := by intro v h; simp at h
  }

def Closed.frontier {n : Nat} {g : Graph n} {start : Fin n}
    (found : Closed g start) : List (Fin n) :=
  found.visited.filter g.relevant

/-- Every returned target has an executable path that stops there. -/
def Closed.target {n : Nat} {g : Graph n} {start v : Fin n}
    (found : Closed g start) (mem : v ∈ found.frontier) : Target g start := {
  node := v
  path := found.path v (List.mem_filter.mp mem).1
  stop := by simpa using (List.mem_filter.mp mem).2
}

/-- Every stopped path reaches a returned target. This includes cyclic CFGs. -/
theorem Closed.complete {n : Nat} {g : Graph n} {start v : Fin n}
    (found : Closed g start) (path : Prefix g start v)
    (stop : g.relevant v = true) : v ∈ found.frontier := by
  have visited : v ∈ found.visited := by
    clear stop
    induction path with
    | root => exact found.root
    | step before neutral edge ih => exact found.closed _ ih neutral _ edge
  exact List.mem_filter.mpr ⟨visited, by simpa using stop⟩

/-- Empty cached frontiers cannot hide a reachable relevant boundary. -/
theorem empty_has_no_target {n : Nat} {g : Graph n} {start v : Fin n}
    (found : Closed g start) (empty : found.frontier = [])
    (path : Prefix g start v) (stop : g.relevant v = true) : False := by
  have mem := found.complete path stop
  simp [empty] at mem

/-- Any valid cached result has exactly the same targets as a fresh search. -/
theorem cache_extensional {n : Nat} {g : Graph n} {start v : Fin n}
    (cached fresh : Closed g start) :
    v ∈ cached.frontier ↔ v ∈ fresh.frontier := by
  constructor
  · intro h
    exact fresh.complete (cached.target h).path (cached.target h).stop
  · intro h
    exact cached.complete (fresh.target h).path (fresh.target h).stop

/-- The type fixes graph/base/direction/view. A runtime cache must enforce that scope. -/
def RouteCache {n : Nat} (g : Graph n) := (start : Fin n) → Option (Closed g start)

def lookup {n : Nat} (g : Graph n) (cache : RouteCache g) (start : Fin n) :
    Closed g start :=
  match cache start with
  | some found => found
  | none => search g start

theorem lookup_exact {n : Nat} (g : Graph n) (cache : RouteCache g)
    (start v : Fin n) :
    v ∈ (lookup g cache start).frontier ↔ v ∈ (search g start).frontier :=
  cache_extensional _ _

/-- Full-key identity is explicit. Protection is an ordered annotation, not equality. -/
structure Cell where
  premise : Nat
  group : Nat
  geometry : Nat
  layer : Nat
  deriving DecidableEq, BEq, Repr

/-- 0 = absent; 1 = present; 2 = present and protected. -/
abbrev Level := Fin 3
abbrev Results := Nat → Cell → Level

structure Offered where
  cell : Cell
  level : Level
  deriving DecidableEq, BEq, Repr

/-- Only the producer row changes. The returned delta can be a protection upgrade. -/
def admit (old : Results) (producer : Nat) (offer : Offered) :
    Results × Option Offered :=
  if old producer offer.cell < offer.level then
    (fun s c => if s = producer ∧ c = offer.cell then offer.level else old s c,
      some offer)
  else (old, none)

theorem admit_idempotent (old : Results) (s : Nat) (offer : Offered) :
    (admit (admit old s offer).1 s offer).2 = none := by
  unfold admit
  split
  · simp
  · simp_all

theorem admit_preserves_other (old : Results) (s t : Nat) (offer : Offered)
    (c : Cell) (other : t ≠ s ∨ c ≠ offer.cell) :
    (admit old s offer).1 t c = old t c := by
  unfold admit
  split
  · dsimp only
    split
    · rename_i h; exact False.elim (other.elim (fun ht => ht h.1) (fun hc => hc h.2))
    · rfl
  · rfl

theorem duplicate_has_no_delta (old : Results) (s : Nat) (offer : Offered)
    (known : offer.level ≤ old s offer.cell) : (admit old s offer).2 = none := by
  simp [admit, Fin.not_lt.mpr known]

theorem protection_upgrade_is_fresh (old : Results) (s : Nat) (c : Cell)
    (known : old s c = 1) :
    (admit old s ⟨c, 2⟩).2 = some ⟨c, 2⟩ := by
  simp [admit, known]

/-- A fixed ordinary/protection cell has at most two fresh nonempty levels. -/
theorem no_three_fresh_levels (a b c : Level)
    (first : (0 : Level) < a) (second : a < b) (third : b < c) : False := by
  have bound := c.isLt
  change 0 < a.val at first
  change a.val < b.val at second
  change b.val < c.val at third
  omega

/-- Fanout starts after the producer. Destinations have no input admission. -/
def afterTargets {n : Nat} (g : Graph n) (s : Fin n) : List (Fin n) :=
  (g.next s).flatMap fun next => (search g next).frontier

structure Delivery (n : Nat) where
  target : Fin n
  offered : Offered
  deriving DecidableEq, BEq, Repr

def finish {n : Nat} (g : Graph n) (old : Results) (s : Fin n) (offer : Offered) :
    Results × List (Delivery n) :=
  let admitted := admit old s.val offer
  (admitted.1, match admitted.2 with
    | none => []
    | some fresh => (afterTargets g s).map fun t => ⟨t, fresh⟩)

theorem after_sound {n : Nat} (g : Graph n) (s t : Fin n)
    (mem : t ∈ afterTargets g s) :
    ∃ next, next ∈ g.next s ∧ t ∈ (search g next).frontier := by
  exact List.mem_flatMap.mp mem

/-- Every old successor route receives the fresh result; no path is missed. -/
theorem fanout_complete {n : Nat} (g : Graph n) (old : Results) (s next t : Fin n)
    (offer : Offered) (fresh : old s.val offer.cell < offer.level)
    (edge : next ∈ g.next s) (path : Prefix g next t) (stop : g.relevant t = true) :
    ⟨t, offer⟩ ∈ (finish g old s offer).2 := by
  have frontier := (search g next).complete path stop
  have mem : t ∈ afterTargets g s := List.mem_flatMap.mpr ⟨next, edge, frontier⟩
  simp [finish, admit, fresh, mem]

/-- Re-evaluating a relevant node is allowed; its identical output has no fanout. -/
theorem identity_cycle_gate {n : Nat} (g : Graph n) (old : Results)
    (s : Fin n) (offer : Offered) :
    (finish g (finish g old s offer).1 s offer).2 = [] := by
  have idem := admit_idempotent old s.val offer
  simp only [finish] at *
  rw [idem]

/-- Source/entry inputs have no result-store effect before execution. -/
def emptyResults : Results := fun _ _ => 0

def testCell : Cell := ⟨1, 2, 3, 0⟩
def unprotected : Offered := ⟨testCell, 1⟩

/-- Initial premarking at the producer would incorrectly suppress its first identity. -/
example : (admit emptyResults 0 unprotected).2 = some unprotected := by decide
example : (admit (admit emptyResults 0 unprotected).1 0 unprotected).2 = none := by decide

/-- Two paths stop at the same relevant join. No destination input gate is used. -/
def diamond : Graph 4 where
  next v := match v.val with
    | 0 => [1, 2]
    | 1 => [3]
    | 2 => [3]
    | _ => []
  relevant v := v.val == 3

example : (search diamond 0).frontier = [3] := by
  simp! [search, bfs_visits, visits, diamond, Closed.frontier, remove, List.finRange_succ, List.finRange_zero, Fin.succ] <;> decide
example : (afterTargets diamond 0) = [3, 3] := by
  simp! [afterTargets, search, bfs_visits, visits, diamond, Closed.frontier, remove, List.finRange_succ, List.finRange_zero, Fin.succ] <;> decide
example : (finish diamond emptyResults 0 unprotected).2 =
    [⟨3, unprotected⟩, ⟨3, unprotected⟩] := by
  simp! [finish, admit, emptyResults, unprotected, afterTargets, search, bfs_visits, visits, diamond, Closed.frontier, remove, List.finRange_succ, List.finRange_zero, Fin.succ] <;> decide
example : (finish diamond (finish diamond emptyResults 0 unprotected).1 0 unprotected).2 = [] := by decide

/-- A relevant identity branch loops through one neutral instruction. -/
def identityLoop : Graph 2 where
  next v := if v.val == 0 then [1] else [0]
  relevant v := v.val == 0

example : (search identityLoop 1).frontier = [0] := by
  simp! [search, bfs_visits, visits, identityLoop, Closed.frontier, remove, List.finRange_succ, List.finRange_zero, Fin.succ] <;> decide
example : (finish identityLoop emptyResults 0 unprotected).2 = [⟨0, unprotected⟩] := by
  simp! [finish, admit, emptyResults, unprotected, afterTargets, search, bfs_visits, visits, identityLoop, Closed.frontier, remove, List.finRange_succ, List.finRange_zero, Fin.succ] <;> decide
example : (finish identityLoop (finish identityLoop emptyResults 0 unprotected).1
    0 unprotected).2 = [] := by decide

/-- A closed neutral cycle has no manufactured exit or summary. -/
def emptyCycle : Graph 2 where
  next v := if v.val == 0 then [1] else [0]
  relevant _ := false

example : (search emptyCycle 0).frontier = [] := by
  simp! [search, bfs_visits, visits, emptyCycle, Closed.frontier, remove, List.finRange_succ, List.finRange_zero, Fin.succ] <;> decide
example : (finish emptyCycle emptyResults 0 unprotected).2 = [] := by
  simp! [finish, admit, emptyResults, unprotected, afterTargets, search, bfs_visits, visits, emptyCycle, Closed.frontier, remove, List.finRange_succ, List.finRange_zero, Fin.succ] <;> decide

/-- A relevant start is executed; its successor search does not reapply it. -/
example : (search identityLoop 0).frontier = [0] := by
  simp! [search, bfs_visits, visits, identityLoop, Closed.frontier, remove, List.finRange_succ, List.finRange_zero, Fin.succ] <;> decide

#print axioms search
#print axioms Closed.complete
#print axioms cache_extensional
#print axioms identity_cycle_gate

end CachedCfgDelivery
