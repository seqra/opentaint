/- Selected conservative boundary collector, 28 October 2026.
   Trace observations stand for bounded STATIC input, intermediate static
   operation output, and final pre-drop result. Candidates remain thin IDs
   until final prune. Common/private-B lists are views, not a second archive.
   The AP/JVM observers and actual call bindings are explicit adapters.
   No complete analyzer soundness theorem is claimed. -/
import «proposals».«restricted-demand».PreExitGuidanceCandidate
import «proposals».«restricted-demand».StaticClosure

namespace KilledStaticWrites
set_option autoImplicit false

abbrev Vertex := PreExitGuidanceCandidate.Vertex

/-- signature names the complete canonical initial/image/mark-relation key.
    It is not a new runtime mark, support flag, Facts packet or callback. -/
structure Key where
  owner : Nat
  original : Vertex
  image : Vertex
  signature : Nat
  deriving DecidableEq, Repr

def Key.edge (key : Key) : PreExitGuidanceCandidate.Edge :=
  ⟨key.owner, key.original, key.image⟩

inductive Event where
  | entered (key : Key)
  | produced (key : Key)
  | result (key : Key)
  | retained (common privateB : List Key)
  deriving DecidableEq, Repr

structure State where
  pending : List Key := []
  common : List Key := []
  privateB : List Key := []
  deriving DecidableEq, Repr

def addPending (key : Key) (keys : List Key) : List Key :=
  if key ∈ keys then keys else key :: keys

def step (state : State) : Event → State
  | .entered key | .produced key | .result key =>
      { state with pending := addPending key state.pending }
  | .retained common privateB => { state with common, privateB }

def run : List Event → State → State
  | [], state => state
  | event :: rest, state => run rest (step state event)

/-- Proof witness only. The implementation does not retain this trace. -/
def beforeKeys : List Event → List Key
  | [] => []
  | .entered key :: rest | .produced key :: rest | .result key :: rest => key :: beforeKeys rest
  | .retained _ _ :: rest => beforeKeys rest

def survivors (state : State) : List Key := state.common ++ state.privateB

def finalKilled (state : State) : List Key :=
  state.pending.filter (fun key => decide (key ∉ survivors state))

def inventory (state : State) : List Key := survivors state ++ finalKilled state

theorem addPending_mem (key other : Key) (keys : List Key) :
    key ∈ addPending other keys ↔ key = other ∨ key ∈ keys := by
  by_cases member : other ∈ keys <;> simp_all [addPending]

theorem pending_exact (trace : List Event) (state : State) (key : Key) :
    key ∈ (run trace state).pending ↔ key ∈ beforeKeys trace ∨ key ∈ state.pending := by
  induction trace generalizing state with
  | nil => simp [run, beforeKeys]
  | cons event rest ih =>
      rw [run, ih]
      cases event <;> simp [beforeKeys, step, addPending_mem, or_assoc, or_left_comm, or_comm]

theorem final_killed_exact (trace : List Event) (key : Key) :
    key ∈ finalKilled (run trace {}) ↔
      key ∈ beforeKeys trace ∧ key ∉ survivors (run trace {}) := by
  simp [finalKilled, pending_exact]

theorem before_covered (trace : List Event) (key : Key) (observed : key ∈ beforeKeys trace) :
    key ∈ inventory (run trace {}) := by
  by_cases survived : key ∈ survivors (run trace {})
  · exact List.mem_append.mpr (.inl survived)
  · exact List.mem_append.mpr (.inr ((final_killed_exact trace key).mpr ⟨observed, survived⟩))

/-- The recovered inventory key is literally the observed key. No field,
    original, owner or colored relation is changed by the collector. -/
def recover (trace : List Event) (key : Key) (observed : key ∈ beforeKeys trace) :
    { recovered : Key // recovered = key ∧ recovered ∈ inventory (run trace {}) } :=
  ⟨key, rfl, before_covered trace key observed⟩

theorem killed_has_observed_owner (trace : List Event) (owner : Nat)
    (owned : ∀ key, key ∈ beforeKeys trace → key.owner = owner)
    (key : Key) (killed : key ∈ finalKilled (run trace {})) : key.owner = owner :=
  owned key ((final_killed_exact trace key).mp killed).1

theorem killed_disjoint_survivors (trace : List Event) (key : Key)
    (killed : key ∈ finalKilled (run trace {})) : key ∉ survivors (run trace {}) :=
  ((final_killed_exact trace key).mp killed).2

/-- Every observed key is covered after any deterministic key projection.
    The adapter must prove that its projection preserves the needed AP row. -/
theorem projected_coverage {Row : Type} (project : Key → Row) (trace : List Event)
    (row : Row) (member : row ∈ (beforeKeys trace).map project) :
    row ∈ (inventory (run trace {})).map project := by
  obtain ⟨key, observed, same⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨key, before_covered trace key observed, same⟩

theorem readers_and_writers_covered {Row : Type} (project : Key → Row)
    (readers : List Row) (trace : List Event) (row : Row)
    (member : row ∈ readers ++ (beforeKeys trace).map project) :
    row ∈ readers ++ (inventory (run trace {})).map project := by
  rcases List.mem_append.mp member with reader | writer
  · exact List.mem_append.mpr (.inl reader)
  · exact List.mem_append.mpr (.inr (projected_coverage project trace row writer))

/-- One already validated actual call application. Both keys are complete:
    in particular, caller.image includes the actual AP delta and field bound.
    This is not a prescan call-graph edge or an unchanged-target assumption. -/
structure ActualBindingStep where
  port : Nat
  child : Key
  caller : Key
  deriving DecidableEq, Repr

/-- BIND is a seed-only phase. It can bind an observed writer and recursively
    bind that writer in callers. It cannot bind a STATICMIDDLE composition. -/
inductive BoundSeed (roots : List Key) (bindings : List ActualBindingStep) : Key → Type where
  | seed {key : Key} (member : key ∈ roots)
      (staticImage : PreExitGuidanceCandidate.isStatic key.image = true) :
      BoundSeed roots bindings key
  | caller {binding : ActualBindingStep} (actual : binding ∈ bindings)
      (nonstatic : PreExitGuidanceCandidate.isStatic binding.child.original = false)
      (staticImage : PreExitGuidanceCandidate.isStatic binding.caller.image = true)
      (body : BoundSeed roots bindings binding.child) :
      BoundSeed roots bindings binding.caller

def moveBound {old fresh : List Key} {bindings : List ActualBindingStep}
    (capture : ∀ key, key ∈ old → key ∈ fresh) {key : Key}
    (proof : BoundSeed old bindings key) : BoundSeed fresh bindings key :=
  match proof with
  | .seed member hs => .seed (capture _ member) hs
  | .caller actual hn hs body => .caller actual hn hs (moveBound capture body)

/-- Every bound key is a primitive key or an explicit complete caller key.
    Thus actual binding cannot invent an endpoint outside this finite universe. -/
theorem bound_finite_universe {roots : List Key} {bindings : List ActualBindingStep}
    {key : Key} (proof : BoundSeed roots bindings key) :
    key ∈ roots ++ bindings.map ActualBindingStep.caller := by
  cases proof with
  | seed member _ => exact List.mem_append.mpr (.inl member)
  | caller actual _ _ _ =>
      exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨_, actual, rfl⟩))

theorem bound_static_image {roots : List Key} {bindings : List ActualBindingStep}
    {key : Key} (proof : BoundSeed roots bindings key) :
    PreExitGuidanceCandidate.isStatic key.image = true := by
  cases proof with
  | seed _ hs => exact hs
  | caller _ _ hs _ => exact hs

/-- The adapter exports a completed, finite seed inventory before composition.
    derive is executable provenance; complete is the binding-saturation contract.
    Neither field asserts an AP reassociation law. -/
structure FrozenSeeds (roots : List Key) (bindings : List ActualBindingStep) where
  keys : List Key
  derive : ∀ key, key ∈ keys → BoundSeed roots bindings key
  complete : ∀ key, BoundSeed roots bindings key → key ∈ keys

theorem frozenCapture (trace : List Event) (bindings : List ActualBindingStep)
    (old : FrozenSeeds (beforeKeys trace) bindings)
    (fresh : FrozenSeeds (inventory (run trace {})) bindings)
    (key : Key) (member : key ∈ old.keys) : key ∈ fresh.keys :=
  fresh.complete key (moveBound (before_covered trace) (old.derive key member))

/-- Reuse old guidance transport only AFTER seed BIND has finished. The empty
    binding list excludes the old bindW constructor from this frozen phase. -/
def transportFrozenGuide {old fresh : List PreExitGuidanceCandidate.Edge}
    (capture : ∀ row, row ∈ old → row ∈ fresh)
    {calls : List PreExitGuidanceCandidate.Call} {m : Nat} {a b : Vertex}
    (route : PreExitGuidanceCandidate.Guide old calls [] m a b) :
    PreExitGuidanceCandidate.Guide fresh calls [] m a b :=
  PreExitGuidanceCandidate.transport capture route

/-- Ordinary static closure transport; all endpoint, owner and mark instances
    stay fixed. A nonstatic caller endpoint must already be caller-bound. -/
def moveEager {old fresh : List StaticDemandClosure.Edge} {calls : List StaticDemandClosure.Call}
    (capture : ∀ row, row ∈ old → row ∈ fresh) {m : Nat} {a b : StaticDemandClosure.Vertex}
    (route : StaticDemandClosure.Eager old calls m a b) : StaticDemandClosure.Eager fresh calls m a b :=
  match route with
  | .seed member => .seed (capture _ member)
  | .inherit call hs ht body => .inherit call hs ht (moveEager capture body)
  | .compose hs left right => .compose hs (moveEager capture left) (moveEager capture right)

/-- Exact eager/factored equality concerns the original three closure rules
    over frozen seeds. It does not commute AP binding with composition. -/
def transportFactored {old fresh : List StaticDemandClosure.Edge}
    (capture : ∀ row, row ∈ old → row ∈ fresh)
    {calls : List StaticDemandClosure.Call} {m : Nat} {a b : StaticDemandClosure.Vertex}
    (route : StaticDemandClosure.Eager old calls m a b) :
    StaticDemandClosure.Path fresh calls m a b :=
  StaticDemandClosure.factor (moveEager capture route)

/-- Relational origin factorization after a real static read. Local transfer
    extends only the reader half; the same static value and origin remain. -/
structure LocalRead (I S L : Type) (front : I → S → Prop) (reader : S → L → Prop)
    (i : I) (point : L) where
  middle : S
  prefixHolds : front i middle
  readHolds : reader middle point

def extendRead {I S L N : Type} {front : I → S → Prop} {reader : S → L → Prop}
    {transfer : L → N → Prop} {i : I} {point : L} {next : N}
    (read : LocalRead I S L front reader i point) (moved : transfer point next) :
    LocalRead I S N front (fun static result => ∃ reached, reader static reached ∧ transfer reached result) i next :=
  ⟨read.middle, read.prefixHolds, ⟨point, read.readHolds, moved⟩⟩

/-- A later write may use a static original in the new core. The old nonstatic
    original is recovered by composing its saved writer relation with this B relation. -/
def splitReadWrite {I S L T : Type} {front : I → S → Prop} {reader : S → L → Prop}
    {write : L → T → Prop} {i : I} {point : L} {target : T}
    (read : LocalRead I S L front reader i point) (written : write point target) :
    { middle : S // front i middle ∧ ∃ reached, reader middle reached ∧ write reached target } :=
  ⟨read.middle, read.prefixHolds, ⟨point, read.readHolds, written⟩⟩

/-- Reuse the concrete call split. Input/output bindings and their witnesses
    remain explicit; only the static middle is shared. -/
def splitCall {I A S B O : Type} {input : I → A → Prop} {writer : A → S → Prop}
    {reader : S → B → Prop} {output : B → O → Prop} {i : I} {o : O}
    (witness : PreExitGuidanceCandidate.CallWitness I A S B O input writer reader output i o) :
    PreExitGuidanceCandidate.SplitCallWitness I A S B O input writer reader output i o :=
  PreExitGuidanceCandidate.splitCall witness

def sample : Key := ⟨0, .ordinary 3 7, .static 4 7, 10⟩
def otherColor : Key := { sample with signature := 11 }
def otherOwner : Key := { sample with owner := 1 }
def copied : Key := ⟨0, .static 4 7, .static 5 7, 12⟩

/-- An actual call can change both owner and bounded static image. The caller
    key is supplied by the AP binding adapter, not copied from the child. -/
def boundSample : Key := ⟨1, .ordinary 8 7, .static 9 7, 30⟩
def actualSample : ActualBindingStep := ⟨17, sample, boundSample⟩
def changedBoundImage : BoundSeed [sample] [actualSample] boundSample :=
  .caller (binding := actualSample) (by simp) rfl rfl (.seed (by simp [actualSample]) rfl)

theorem complete_exit_kill_keeps_key : finalKilled (run [.entered sample] {}) = [sample] := by decide

theorem later_survivor_is_pruned :
    finalKilled (run [.entered sample, .retained [sample] [], .produced sample] {}) = [] := by decide

theorem intermediate_exit_write_is_kept :
    finalKilled (run [.produced copied, .retained [] []] {}) = [copied] := by decide

theorem owner_and_color_do_not_discharge_key :
    finalKilled (run [.entered sample, .retained [otherColor,otherOwner] []] {}) = [sample] := by decide

/-- A compacted colored row can disappear from the common inventory.
    Conservative pending retains its key until the final snapshot. -/
theorem nonmonotone_survivors_keep_candidate :
    finalKilled (run [.entered sample, .retained [sample] [], .retained [] []] {}) = [sample] := by decide

#print axioms addPending_mem
#print axioms pending_exact
#print axioms final_killed_exact
#print axioms before_covered
#print axioms recover
#print axioms killed_has_observed_owner
#print axioms killed_disjoint_survivors
#print axioms projected_coverage
#print axioms readers_and_writers_covered
#print axioms moveBound
#print axioms bound_finite_universe
#print axioms bound_static_image
#print axioms frozenCapture
#print axioms transportFrozenGuide
#print axioms moveEager
#print axioms transportFactored
#print axioms extendRead
#print axioms splitReadWrite
#print axioms splitCall
#print axioms changedBoundImage
#print axioms complete_exit_kill_keeps_key
#print axioms later_survivor_is_pruned
#print axioms intermediate_exit_write_is_kept
#print axioms owner_and_color_do_not_discharge_key
#print axioms nonmonotone_survivors_keep_candidate
end KilledStaticWrites
