import Std

/-!
Pure usefulness over a supplied finite graph of frozen NORMAL records.
Vertices are opaque COMPLETE query states: direction, port, whole original,
layer, marks, E/mx, protection and call context belong to the adapter key.
NORMAL describes the supplied record, not necessarily the fact layer.
Terminals denote supplied current-demand compatibility. Querying has no
analyzer callbacks, initial admission, rule execution or publication effects.

Reverse breadth-first waves retain Type-valued executable route witnesses.
The canonical finite scan is a reference, not a production implementation.
The n-vertex bound does NOT prove that an AP graph is small or correctly
extracted. Unchecked prefix growth is not such a supplied finite graph.
Current ND edges and pending bindings are not included in this contract.
-/
/- Reference investigation only. The selected protocol uses native persisted
   replay; this module does not specify a new runtime service. -/
namespace LoopFragments.Usefulness
set_option autoImplicit false

structure Graph (n : Nat) where
  normal : Fin n → Fin n → Bool
  demand : Fin n → Bool

variable {n : Nat}

inductive Route (g : Graph n) : Fin n → Type where
  | demand (v : Fin n) (terminal : g.demand v = true) : Route g v
  | normal (v w : Fin n) (edge : g.normal v w = true) (tail : Route g w) : Route g v

inductive Reaches (g : Graph n) : Fin n → Prop where
  | demand (v : Fin n) (terminal : g.demand v = true) : Reaches g v
  | normal (v w : Fin n) (edge : g.normal v w = true) (tail : Reaches g w) : Reaches g v

def Route.vertices {g : Graph n} {v : Fin n} : Route g v → List (Fin n)
  | .demand node _ => [node]
  | .normal node _ _ tail => node :: tail.vertices

def Route.hops {g : Graph n} {v : Fin n} : Route g v → Nat
  | .demand _ _ => 0
  | .normal _ _ _ tail => tail.hops + 1

theorem Route.reaches {g : Graph n} {v : Fin n} (route : Route g v) : Reaches g v := by
  induction route with
  | demand node terminal => exact .demand node terminal
  | normal node next edge tail ih => exact .normal node next edge ih

def Table (g : Graph n) := (v : Fin n) → Option (Route g v)

def seed (g : Graph n) : Table g := fun v =>
  if terminal : g.demand v = true then some (.demand v terminal) else none

def nextRoute (g : Graph n) (known : Table g) (v : Fin n) : List (Fin n) → Option (Route g v)
  | [] => none
  | w :: rest =>
      if edge : g.normal v w = true then
        match known w with
        | some tail => some (.normal v w edge tail)
        | none => nextRoute g known v rest
      else nextRoute g known v rest

def wave (g : Graph n) (known : Table g) : Table g := fun v =>
  match known v with
  | some route => some route
  | none => nextRoute g known v (List.finRange n)

def search (g : Graph n) : Nat → Table g
  | 0 => seed g
  | fuel + 1 => wave g (search g fuel)

def discovered (g : Graph n) (fuel : Nat) : List (Fin n) :=
  (List.finRange n).filter fun v => (search g fuel v).isSome

/-- Result certificates do not authorize new actual summary rows. -/
def query (g : Graph n) (v : Fin n) : Option (Route g v) := search g n v

theorem nextRoute_iff (g : Graph n) (known : Table g) (v : Fin n) (nodes : List (Fin n)) :
    (nextRoute g known v nodes).isSome = true ↔
      ∃ w ∈ nodes, g.normal v w = true ∧ (known w).isSome = true := by
  induction nodes with
  | nil => simp [nextRoute]
  | cons w rest ih =>
      by_cases edge : g.normal v w = true
      · cases saved : known w with
        | none => simp [nextRoute, edge, saved, ih]
        | some route => simp [nextRoute, edge, saved]
      · simp [nextRoute, edge, ih]

theorem wave_iff (g : Graph n) (known : Table g) (v : Fin n) :
    (wave g known v).isSome = true ↔
      (known v).isSome = true ∨ ∃ w, g.normal v w = true ∧ (known w).isSome = true := by
  cases saved : known v with
  | none => simp [wave, saved, nextRoute_iff]
  | some route => simp [wave, saved]

theorem discovered_iff (g : Graph n) (fuel : Nat) (v : Fin n) :
    v ∈ discovered g fuel ↔ (search g fuel v).isSome = true := by
  simp [discovered]

theorem search_keeps (g : Graph n) (fuel : Nat) (v : Fin n)
    (present : (search g fuel v).isSome = true) :
    (search g (fuel + 1) v).isSome = true :=
  (wave_iff g (search g fuel) v).mpr (Or.inl present)

theorem filter_sublist_of_imp {α : Type} (p q : α → Bool) (nodes : List α)
    (implies : ∀ v, p v = true → q v = true) :
    (nodes.filter p).Sublist (nodes.filter q) := by
  induction nodes with
  | nil => exact .refl []
  | cons v rest ih =>
      cases hp : p v <;> cases hq : q v <;> simp only [List.filter_cons, hp, hq, Bool.false_eq_true,
        ↓reduceIte]
      · exact ih
      · exact .cons v ih
      · exact False.elim (by have yes := implies v hp; simp [hq] at yes)
      · exact .cons_cons v ih

theorem discovered_sublist (g : Graph n) (fuel : Nat) :
    (discovered g fuel).Sublist (discovered g (fuel + 1)) :=
  filter_sublist_of_imp _ _ _ (search_keeps g fuel)

theorem discovered_length_le (g : Graph n) (fuel : Nat) :
    (discovered g fuel).length ≤ n := by
  have bound := (List.filter_sublist (p := fun v => (search g fuel v).isSome)
    (l := List.finRange n)).length_le
  simpa [discovered] using bound

theorem stable_table (g : Graph n) (fuel : Nat)
    (stable : discovered g (fuel + 1) = discovered g fuel) :
    search g (fuel + 1) = search g fuel := by
  funext v
  cases old : search g fuel v with
  | some route => simp [search, wave, old]
  | none =>
      cases fresh : search g (fuel + 1) v with
      | none => rfl
      | some route =>
          have member : v ∈ discovered g (fuel + 1) := (discovered_iff g _ _).mpr (by simp [fresh])
          rw [stable] at member
          have impossible := (discovered_iff g _ _).mp member
          simp [old] at impossible

theorem stable_forever (g : Graph n) (fuel : Nat)
    (stable : discovered g (fuel + 1) = discovered g fuel) (extra : Nat) :
    search g (fuel + extra) = search g fuel := by
  have fixed := stable_table g fuel stable
  induction extra with
  | zero => simp
  | succ extra ih =>
      change wave g (search g (fuel + extra)) = search g fuel
      rw [ih]
      exact fixed

theorem unstable_strict_growth (g : Graph n) (fuel : Nat)
    (unstable : discovered g (fuel + 1) ≠ discovered g fuel) :
    (discovered g fuel).length < (discovered g (fuel + 1)).length := by
  have sub := discovered_sublist g fuel
  have le := sub.length_le
  have unequal : (discovered g fuel).length ≠ (discovered g (fuel + 1)).length := by
    intro equal
    exact unstable (sub.eq_of_length equal).symm
  omega

/-- A finite n-vertex graph admits at most n strict discovery waves. -/
theorem finite_saturation (g : Graph n) : discovered g (n + 1) = discovered g n := by
  by_cases stable : discovered g (n + 1) = discovered g n
  · exact stable
  · have every : ∀ fuel, fuel ≤ n → discovered g (fuel + 1) ≠ discovered g fuel := by
      intro fuel within early
      have now := stable_forever g fuel early (n - fuel)
      have later := stable_forever g fuel early (n + 1 - fuel)
      have a : fuel + (n - fuel) = n := by omega
      have b : fuel + (n + 1 - fuel) = n + 1 := by omega
      rw [a] at now
      rw [b] at later
      apply stable
      unfold discovered
      rw [later, now]
    have lower : ∀ fuel, fuel ≤ n + 1 → fuel ≤ (discovered g fuel).length := by
      intro fuel
      induction fuel with
      | zero => intro _; omega
      | succ fuel ih =>
          intro within
          have previous := ih (by omega)
          have strict := unstable_strict_growth g fuel (every fuel (by omega))
          omega
    have below := lower (n + 1) (by omega)
    have above := discovered_length_le g (n + 1)
    omega

theorem query_closed (g : Graph n) (v w : Fin n)
    (edge : g.normal v w = true) (useful : (query g w).isSome = true) :
    (query g v).isSome = true := by
  have next := (wave_iff g (search g n) v).mpr (Or.inr ⟨w, edge, useful⟩)
  have fixed := stable_table g n (finite_saturation g)
  change (search g (n + 1) v).isSome = true at next
  rw [fixed] at next
  exact next

theorem query_terminal (g : Graph n) (v : Fin n) (terminal : g.demand v = true) :
    (query g v).isSome = true := by
  have seeded : (search g 0 v).isSome = true := by simp [search, seed, terminal]
  have keep : ∀ fuel, (search g fuel v).isSome = true := by
    intro fuel
    induction fuel with
    | zero => exact seeded
    | succ fuel ih => exact search_keeps g fuel v ih
  exact keep n

theorem query_complete (g : Graph n) (v : Fin n) (path : Reaches g v) :
    (query g v).isSome = true := by
  induction path with
  | demand node terminal => exact query_terminal g node terminal
  | normal node next edge tail ih => exact query_closed g node next edge ih

theorem query_sound (g : Graph n) (v : Fin n) (present : (query g v).isSome = true) :
    Reaches g v := by
  cases found : query g v with
  | none => simp [found] at present
  | some route => exact route.reaches

theorem query_iff (g : Graph n) (v : Fin n) :
    (query g v).isSome = true ↔ Reaches g v :=
  ⟨query_sound g v, query_complete g v⟩

theorem rejected_has_no_path (g : Graph n) (v : Fin n) (rejected : query g v = none) :
    ¬ Reaches g v := by
  intro path
  have present := query_complete g v path
  simp [rejected] at present

/-- A certificate can be read as an executable data path. -/
def certificate (g : Graph n) (v : Fin n) (path : Reaches g v) :
    { route : Route g v // query g v = some route } :=
  match found : query g v with
  | some route => ⟨route, rfl⟩
  | none => False.elim (rejected_has_no_path g v found path)

theorem nextRoute_hops (g : Graph n) (known : Table g) (v : Fin n)
    (nodes : List (Fin n)) (fuel : Nat)
    (bounded : ∀ w route, known w = some route → route.hops ≤ fuel)
    (result : Route g v) (found : nextRoute g known v nodes = some result) :
    result.hops ≤ fuel + 1 := by
  induction nodes with
  | nil => simp [nextRoute] at found
  | cons w rest ih =>
      by_cases edge : g.normal v w = true
      · cases saved : known w with
        | none => exact ih (by simpa [nextRoute, edge, saved] using found)
        | some tail =>
            have same : Route.normal v w edge tail = result := by
              simpa [nextRoute, edge, saved] using found
            rw [← same]
            exact Nat.succ_le_succ (bounded w tail saved)
      · exact ih (by simpa [nextRoute, edge] using found)

theorem search_hops (g : Graph n) (fuel : Nat) (v : Fin n)
    (result : Route g v) (found : search g fuel v = some result) : result.hops ≤ fuel := by
  induction fuel generalizing v with
  | zero =>
      by_cases terminal : g.demand v = true
      · have same : Route.demand v terminal = result := by simpa [search, seed, terminal] using found
        rw [← same]
        exact Nat.zero_le _
      · simp [search, seed, terminal] at found
  | succ fuel ih =>
      cases old : search g fuel v with
      | some previous =>
          have same : previous = result := by simpa [search, wave, old] using found
          rw [← same]
          exact Nat.le_trans (ih v previous old) (Nat.le_succ _)
      | none =>
          exact nextRoute_hops g (search g fuel) v (List.finRange n) fuel ih result
            (by simpa [search, wave, old] using found)

theorem query_hops (g : Graph n) (v : Fin n) (route : Route g v)
    (found : query g v = some route) : route.hops ≤ n := search_hops g n v route found

/-- A supplied demand terminal is not expanded through more NORMAL records. -/
theorem search_terminal_exact (g : Graph n) (fuel : Nat) (v : Fin n)
    (terminal : g.demand v = true) : search g fuel v = some (.demand v terminal) := by
  induction fuel with
  | zero => simp [search, seed, terminal]
  | succ fuel ih => simp [search, wave, ih]

def Route.stopsAtFirst {g : Graph n} {v : Fin n} : Route g v → Prop
  | .demand _ _ => True
  | .normal node _ _ tail => g.demand node = false ∧ tail.stopsAtFirst

theorem nextRoute_stops (g : Graph n) (known : Table g) (v : Fin n)
    (nodes : List (Fin n)) (notTerminal : g.demand v = false)
    (stops : ∀ w route, known w = some route → route.stopsAtFirst)
    (result : Route g v) (found : nextRoute g known v nodes = some result) :
    result.stopsAtFirst := by
  induction nodes with
  | nil => simp [nextRoute] at found
  | cons w rest ih =>
      by_cases edge : g.normal v w = true
      · cases saved : known w with
        | none => exact ih (by simpa [nextRoute, edge, saved] using found)
        | some tail =>
            have same : Route.normal v w edge tail = result := by
              simpa [nextRoute, edge, saved] using found
            rw [← same]
            exact ⟨notTerminal, stops w tail saved⟩
      · exact ih (by simpa [nextRoute, edge] using found)

theorem search_stops (g : Graph n) (fuel : Nat) (v : Fin n)
    (result : Route g v) (found : search g fuel v = some result) : result.stopsAtFirst := by
  induction fuel generalizing v with
  | zero =>
      by_cases terminal : g.demand v = true
      · have same : Route.demand v terminal = result := by simpa [search, seed, terminal] using found
        rw [← same]
        trivial
      · simp [search, seed, terminal] at found
  | succ fuel ih =>
      cases old : search g fuel v with
      | some previous =>
          have same : previous = result := by simpa [search, wave, old] using found
          rw [← same]
          exact ih v previous old
      | none =>
          have notTerminal : g.demand v = false := by
            cases terminal : g.demand v with
            | false => rfl
            | true => have impossible := search_terminal_exact g fuel v terminal; simp [old] at impossible
          exact nextRoute_stops g (search g fuel) v (List.finRange n) notTerminal ih result
            (by simpa [search, wave, old] using found)

theorem query_stops_at_first_demand (g : Graph n) (v : Fin n) (route : Route g v)
    (found : query g v = some route) : route.stopsAtFirst := search_stops g n v route found

/-- Querying has no analyzer-state component or publication callback. -/
theorem query_is_pure (g : Graph n) (v : Fin n) : (g, query g v).1 = g := rfl

def identityRelay : Graph 3 := {
  normal := fun a b => decide ((a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 2))
  demand := fun v => decide (v.val = 2)
}

theorem identity_chain_reaches_farther_demand :
    identityRelay.demand 0 = false ∧ (query identityRelay 0).isSome = true := by decide

def prefixGrowthWithoutDemand : Graph 4 := {
  normal := fun a b => decide (b.val = a.val + 1 ∨ (a.val = 3 ∧ b.val = 3))
  demand := fun _ => false
}

theorem forward_prefix_growth_without_terminal_is_pruned :
    ∀ v, query prefixGrowthWithoutDemand v = none := by decide

/-- A route certificate proves usefulness only, not C2/C5 or ND permission. -/
theorem usefulness_is_not_a_demand_row (g : Graph n) (v : Fin n)
    (useful : (query g v).isSome = true) : Reaches g v := query_sound g v useful

end LoopFragments.Usefulness
