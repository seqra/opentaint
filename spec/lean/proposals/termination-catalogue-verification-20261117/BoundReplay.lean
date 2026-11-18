import TerminalReplay
import BoundCore

namespace BoundReplay
open NonEmptyPolicy NonEmptyRestriction AlternatingCondition
set_option maxRecDepth 65536
set_option maxHeartbeats 300000000

structure Hop where
  input : Value
  emitted : Value
  next : Value
  deriving DecidableEq, BEq, Repr

structure Slice where
  source : Value
  generate : Color → Seed → List Value
  colors : List Color
  consume : Value → Option Value

def transfers (s : Slice) (input : Value) : List Hop :=
  (s.colors.flatMap (fun m => s.generate m ⟨{input.ap with base := p},input.demand⟩)).filterMap
    fun emitted => (s.consume {emitted with ap := {emitted.ap with base := p}, h := emitted.h || input.h}).map
      fun next => ⟨input,emitted,next⟩

-- Fully enumerate the three body/caller statements. Each result carries
-- the whole ordered sequence of marking outputs and bound inputs.
def routes (s : Slice) : Nat → Value → List (List Hop)
  | 0, _ => [[]]
  | n+1, input => (transfers s input).flatMap fun h =>
    (routes s n h.next).map (h :: ·)

inductive Follows (s : Slice) : Nat → Value → List Hop → Prop
  | done : Follows s 0 input []
  | call : hop ∈ transfers s input → Follows s n hop.next rest →
    Follows s (n+1) input (hop :: rest)

theorem all_routes_of_the_three_calls_are_enumerated
    (route : Follows s n input hops) : hops ∈ routes s n input := by
  induction route with
  | done => simp [routes]
  | @call input hop n rest first _ later =>
    exact List.mem_flatMap.mpr ⟨hop,first,List.mem_map.mpr ⟨rest,later,rfl⟩⟩

-- A route has the same observer seed as the fixture. A final field f
-- output under MAY is observable. Outputs with another full mark are
-- included if the fixture observes them as well.
def receives (s : Slice) (observer : Value → Bool) : List (List Hop) :=
  (routes s 3 s.source).filter fun route => (route.getLast?).any fun h => observer h.next

theorem every_real_observer_route_is_in_the_retirement_catalogue
    (steps : Follows s 3 s.source hops)
    (seen : hops.getLast?.any (fun h => observer h.next) = true) :
    hops ∈ receives s observer :=
  List.mem_filter.mpr ⟨all_routes_of_the_three_calls_are_enumerated steps,seen⟩

structure RunView where
  offers : List (List Value)
  current : List (Ap × Value)
  saved : List (Ap × Value)
  -- Use the precise binding's own row. This must use the prepared C2
  -- family, not the projection of an unrelated row with the same result.
  candidates : Offered → List (Ap × Value)
  replay : Bool → (Ap × Value) → Offered → Option Value

def delivered (view : RunView) (stage : Nat) (hop : Hop) : Bool :=
  let actual : Offered := ⟨{hop.input.ap with base := p},hop.input.demand⟩
  let output : Value :=
    {hop.emitted with
      ap := {hop.emitted.ap with base := p}
      h := hop.emitted.h || hop.input.h}
  let covered := fun packet => packet.any fun n => BoundCore.covers n output
  decide (hop.input ∈ view.offers[stage]!) &&
    decide (hop.next ∈ view.offers[stage+1]!) &&
    (covered ((view.saved ++ (view.candidates actual).filter
      (fun e => decide (e ∈ view.current))).filterMap (fun e => view.replay hop.input.h e actual)))

def witnessed (view : RunView) (route : List Hop) : Bool :=
  route.zipIdx.all fun (hop,stage) => delivered view stage hop

theorem every_checked_route_has_each_bound_hop (view : RunView) (route : List Hop)
    (valid : witnessed view route = true) (h : (hop,stage) ∈ route.zipIdx) :
    delivered view stage hop = true :=
  List.all_eq_true.mp valid _ h

end BoundReplay
