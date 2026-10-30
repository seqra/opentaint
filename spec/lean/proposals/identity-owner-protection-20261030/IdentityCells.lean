import Std

/-!
The exact one-coordinate admission kernel. A coordinate includes the complete
initial image; a different image must use the existing scalar group. Layers
and protection are independent. The final parametric theorem is a delegation
proof, not an axiom about the analyzer's full AP algebra.
-/
namespace IdentityCells

inductive Cell where
  | absent
  | plain
  | guarded
deriving DecidableEq, Repr

structure Scalar where
  present : Bool
  guarded : Bool
deriving DecidableEq, Repr

def decode : Cell → Scalar
  | .absent => ⟨false, false⟩
  | .plain => ⟨true, false⟩
  | .guarded => ⟨true, true⟩

/-- The reference ordinary/annotation set update for one complete coordinate. -/
def scalarAdd (old : Scalar) (offeredProtection : Bool) : Scalar × Option Bool :=
  (⟨true, old.guarded || offeredProtection⟩,
   if !old.present || (offeredProtection && !old.guarded)
   then some offeredProtection else none)

def add (old : Cell) (offeredProtection : Bool) : Cell × Option Bool :=
  match old, offeredProtection with
  | .absent, false => (.plain, some false)
  | .absent, true => (.guarded, some true)
  | .plain, true => (.guarded, some true)
  | .plain, false => (.plain, none)
  | .guarded, _ => (.guarded, none)

theorem exact_state_and_delta (old : Cell) (p : Bool) :
    (decode (add old p).1, (add old p).2) = scalarAdd (decode old) p := by
  cases old <;> cases p <;> rfl

theorem decoded_valid (old : Cell) :
    (decode old).guarded = true → (decode old).present = true := by
  cases old <;> simp [decode]

theorem first_plain_is_fresh : add .absent false = (.plain, some false) := rfl
theorem plain_duplicate : add .plain false = (.plain, none) := rfl
theorem protection_upgrade : add .plain true = (.guarded, some true) := rfl
theorem protected_not_downgraded (p : Bool) :
    add .guarded p = (.guarded, none) := by cases p <;> rfl

def Slots := Fin 2 → Cell
def ScalarSlots := Fin 2 → Scalar
def decodeSlots (s : Slots) : ScalarSlots := fun layer => decode (s layer)

def addAt (s : Slots) (layer : Fin 2) (p : Bool) : Slots × Option Bool :=
  let step := add (s layer) p
  ((fun other => if other = layer then step.1 else s other), step.2)

def scalarAddAt (s : ScalarSlots) (layer : Fin 2) (p : Bool) : ScalarSlots × Option Bool :=
  let step := scalarAdd (s layer) p
  ((fun other => if other = layer then step.1 else s other), step.2)

theorem layers_exact (s : Slots) (layer : Fin 2) (p : Bool) :
    (decodeSlots (addAt s layer p).1, (addAt s layer p).2) =
      scalarAddAt (decodeSlots s) layer p := by
  have h := exact_state_and_delta (s layer) p
  apply Prod.ext
  · funext other
    by_cases same : other = layer
    · subst other
      simpa [decodeSlots, addAt, scalarAddAt] using congrArg Prod.fst h
    · simp [decodeSlots, addAt, scalarAddAt, same]
  · simpa [decodeSlots, addAt, scalarAddAt] using congrArg Prod.snd h

theorem other_layer_unchanged (s : Slots) (layer other : Fin 2) (p : Bool)
    (different : other ≠ layer) : (addAt s layer p).1 other = s other := by
  simp [addAt, different]

/-- The key contains the full premise and the producing statement. -/
def put {Key : Type} [DecidableEq Key] (s : Key → Slots) (key : Key)
    (layer : Fin 2) (p : Bool) : (Key → Slots) × Option Bool :=
  let step := addAt (s key) layer p
  ((fun other => if other = key then step.1 else s other), step.2)

theorem other_producer_unchanged {Key : Type} [DecidableEq Key]
    (s : Key → Slots) (key other : Key) (layer : Fin 2) (p : Bool)
    (different : other ≠ key) : (put s key layer p).1 other = s other := by
  simp [put, different]

def replay (s : Slots) : List (Fin 2 × Bool) :=
  (List.finRange 2).filterMap fun layer => match s layer with
    | .absent => none
    | .plain => some (layer, false)
    | .guarded => some (layer, true)

theorem replay_present (s : Slots) (layer : Fin 2) (p : Bool) :
    (layer, p) ∈ replay s ↔ s layer = (if p then Cell.guarded else .plain) := by
  simp only [replay, List.mem_filterMap]
  constructor
  · rintro ⟨a, _, h⟩
    cases hs : s a <;> simp [hs] at h
    all_goals obtain ⟨rfl, rfl⟩ := h; simpa using hs
  · intro h
    refine ⟨layer, List.mem_finRange _, ?_⟩
    cases p <;> simp_all

/-- A full row is opaque: its admission implementation is reused unchanged. -/
inductive Native (G : Type) where
  | compact (slots : Slots)
  | full (group : G)

def expand {G : Type} (restore : Slots → G) : Native G → G
  | .compact s => restore s
  | .full g => g

def promoteAndAdd {G Input Output : Type} (restore : Slots → G)
    (oldAdd : G → Input → G × Output) (s : Slots) (input : Input) : Native G × Output :=
  let result := oldAdd (restore s) input
  (.full result.1, result.2)

theorem promotion_state_and_delta {G Input Output : Type} (restore : Slots → G)
    (oldAdd : G → Input → G × Output) (s : Slots) (input : Input) :
    (expand restore (promoteAndAdd restore oldAdd s input).1,
       (promoteAndAdd restore oldAdd s input).2) = oldAdd (restore s) input := rfl

def continueFull {G Input Output : Type} (oldAdd : G → Input → G × Output)
    (g : G) (input : Input) : Native G × Output :=
  let result := oldAdd g input
  (.full result.1, result.2)

theorem full_fallback_exact {G Input Output : Type} (restore : Slots → G)
    (oldAdd : G → Input → G × Output) (g : G) (input : Input) :
    (expand restore (continueFull oldAdd g input).1,
       (continueFull oldAdd g input).2) = oldAdd g input := rfl

theorem promotion_never_restores_as_delta {G Input Output : Type}
    (restore : Slots → G) (oldAdd : G → Input → G × Output)
    (s : Slots) (input : Input) :
    (promoteAndAdd restore oldAdd s input).2 = (oldAdd (restore s) input).2 := rfl

def trace (s : Slots) : List (Fin 2 × Bool) → Slots × List (Option Bool)
  | [] => (s, [])
  | (layer, p) :: rest =>
    let now := addAt s layer p
    let later := trace now.1 rest
    (later.1, now.2 :: later.2)

def scalarTrace (s : ScalarSlots) : List (Fin 2 × Bool) → ScalarSlots × List (Option Bool)
  | [] => (s, [])
  | (layer, p) :: rest =>
    let now := scalarAddAt s layer p
    let later := scalarTrace now.1 rest
    (later.1, now.2 :: later.2)

theorem trace_exact (s : Slots) (events : List (Fin 2 × Bool)) :
    (decodeSlots (trace s events).1, (trace s events).2) =
      scalarTrace (decodeSlots s) events := by
  induction events generalizing s with
  | nil => rfl
  | cons event rest ih =>
    rcases event with ⟨layer, p⟩
    have h := layers_exact s layer p
    have hs := congrArg Prod.fst h
    have hd := congrArg Prod.snd h
    simp only [trace, scalarTrace]
    rw [← hs, ← hd]
    have next := ih (addAt s layer p).1
    exact congrArg (fun result => (result.1, (addAt s layer p).2 :: result.2)) next

def empty : Slots := fun _ => .absent

example : (trace empty [(0, false), (0, false), (0, true), (0, false)]).2 =
    [some false, none, some true, none] := by decide
example : (trace empty [(0, true), (1, false), (1, true)]).2 =
    [some true, some false, some true] := by decide
example : 5325214 * (32 + 24 + 48 + 48) = 809432528 := by decide

end IdentityCells
