import Std

namespace MixedOfferCycle
-- Literal empty-E/mx scalar FLOW fragment. Base and physical port are fixed
-- by direction: original p -> ret, opposite ret -> p. No eligibility test.
-- The external offers stay fixed. State.normals is retained and checked for
-- exact point service; infer/step do not schedule replay/caller feedback.
-- Only reached EXACT/STAR/ANY cells have native correspondence checks.
inductive Tail where | exact | star | any | must
  deriving DecidableEq, BEq, Ord, Repr
structure Fact where
  path : List Nat
  tail : Tail := .star
  demand : Bool := false
  deriving DecidableEq, BEq, Ord, Repr
structure Row where
  entry : Fact
  exit : Fact
  deriving DecidableEq, BEq, Ord, Repr
structure Rel where
  initial : Fact
  result : Fact
  deriving DecidableEq, BEq, Ord, Repr
structure Saved where
  opposite : Bool
  relation : Rel
  deriving DecidableEq, BEq, Ord, Repr
structure State where
  opposite : Bool
  rows : List Row
  normals : List Saved
  deriving DecidableEq, Repr

def pre (a b : List Nat) : Bool := a == b.take a.length

def insert [Ord α] (x : α) : List α → List α
 | [] => [x]
 | y::ys => if compare x y != .gt then x::y::ys else y::insert x ys

def sorted [BEq α] [Ord α] (xs : List α) : List α :=
  xs.foldr (fun x ys => if ys.contains x then ys else insert x ys) []

def normal (f : Fact) : Fact :=
  if f.demand && (f.tail == .exact || f.tail == .must) then {f with tail := .any}
  else if f.tail == .exact then {f with tail := .star} else f

def c2 (d a : Fact) : List Fact :=
  if d.path == a.path then
    if d.tail == .any then
      [{path := d.path, tail := if a.tail == .exact then .exact else if a.tail == .must then .must else .star}]
    else if d.tail == .star || d.tail == .exact then [{path := d.path, tail := .exact}] else []
  else if pre d.path a.path && d.tail == .any then
    [{path := a.path.take (d.path.length + 1)}, {path := d.path, tail := .exact}]
  else if pre a.path d.path && (a.tail == .any || a.tail == .must) then
    [{path := d.path, tail := if d.tail == .any then (if a.tail == .must then .must else .star) else .exact}]
  else []

def apply (input : Fact) (read write : List Nat) : Option Fact :=
  if pre read input.path then some {input with path := write ++ input.path.drop read.length}
  else if pre input.path read && input.tail != .exact then
    if input.tail == .must && !input.demand then some {path := write, tail := .must}
    else some {path := write, tail := .any, demand := true}
  else none

def entryOK (d i : Fact) : Bool :=
  if d.path == i.path then i.tail == .star || i.tail == .exact || (d.tail == .any && i.tail == .must)
  else d.tail == .any && pre d.path i.path && i.path.length == d.path.length + 1 && i.tail == .star

def c5 (i raw : Fact) (row : Row) : Option Fact := do
  if !entryOK row.entry i then none else
  let selected ← if pre row.exit.path raw.path then some raw
    else if pre raw.path row.exit.path then
      if raw.tail == .any || raw.tail == .must then some {raw with path := row.exit.path}
      else if raw.tail == .star then some raw else none
    else none
  let result := normal selected
  let budget := row.exit.path.length + 1
  if result.path.length > budget then some {path := result.path.take budget, tail := .any, demand := true}
  else some result

def subsumes (a b : Rel) : Bool := a.initial == b.initial &&
  a.result.demand == b.result.demand && a.result.tail == .any && pre a.result.path b.result.path

def canonical (xs : List Rel) : List Rel :=
  let unique := sorted xs
  unique.filter (fun b => !(unique.any (fun a => a != b && subsumes a b)))

-- Fields: a=0, g=1, f=2, h=3.
def aPath := [0,1]
def cPath := [2,3,3,3]
def body : List (List Nat × List Nat) := [(aPath,cPath),(aPath ++ [2],[])]

def offers (opposite : Bool) : List Fact :=
  if opposite then [{path := cPath, tail := .exact},{path := []}]
  else [{path := aPath, tail := .exact},{path := aPath}]

def infer (state : State) : List Rel := Id.run do
  let initials := sorted (state.rows.flatMap fun row => (offers state.opposite).flatMap fun a => c2 row.entry a)
  let edges := if state.opposite then body.map (fun p => (p.2,p.1)) else body
  let mut results := []
  for initial in initials do
    for edge in edges do
      if let some raw := apply initial edge.1 edge.2 then
        for row in state.rows do
          if let some selected := c5 initial raw row then
            results := {initial := normal initial, result := selected} :: results
  return canonical results

def step (state : State) : State :=
  let admitted := infer state
  let rows := admitted.filterMap fun r => if r.result.demand then some
    {entry := {r.result with demand := false}, exit := r.initial} else none
  let normals := admitted.filterMap fun r => if !r.result.demand then some
    {opposite := state.opposite, relation := r} else none
  {opposite := !state.opposite, rows := sorted rows, normals := sorted (state.normals ++ normals)}

def x : Row := {entry := {path := [0],tail := .any},exit := {path := [2,3,3]}}
def z : Row := {entry := x.entry,exit := {path := []}}
def cutStart : State := {opposite := false,rows := [z],normals := []}
def keepStart : State := {cutStart with rows := [x,z]}
def phaseA : State := step (step (step cutStart))
def phaseB : State := step phaseA

-- This calculates the actual operators above, not an assumed transition table.
theorem cycle_a : step phaseA = phaseB := rfl
theorem cycle_b : step phaseB = phaseA := by decide

inductive InCycle : State → Prop where
 | a : InCycle phaseA
 | b : InCycle phaseB

theorem closed {s : State} (h : InCycle s) : InCycle (step s) := by
  cases h with
  | a => rw [cycle_a]; exact InCycle.b
  | b => rw [cycle_b]; exact InCycle.a

def iterate : Nat → State → State
 | 0,s => s
 | n+1,s => step (iterate n s)

theorem cycle_all_rounds (n : Nat) : InCycle (iterate n phaseA) := by
  induction n with
  | zero => exact InCycle.a
  | succ n ih => exact closed ih

def pointSupported (s : State) : Bool := s.normals.any fun n =>
  let rel := n.relation
  let (read,write) := if n.opposite then (rel.result.path,rel.initial.path) else (rel.initial.path,rel.result.path)
  match apply {path := aPath,tail := .exact} read write with
  | none => false
  | some f => f.path == cPath && f.tail == .exact && !f.demand

theorem baseline_support : pointSupported (step keepStart) = true := by decide
theorem no_cycle_support {s : State} (h : InCycle s) : pointSupported s = false := by
  cases h <;> decide

theorem no_support_at_any_later_round (n : Nat) :
    pointSupported (iterate n phaseA) = false := no_cycle_support (cycle_all_rounds n)

inductive CutReachable : State → Prop where
 | first : CutReachable (step cutStart)
 | a : CutReachable phaseA
 | b : CutReachable phaseB

theorem cut_closed {s : State} (h : CutReachable s) : CutReachable (step s) := by
  cases h with
  | first => have eq : step (step cutStart) = phaseB := by decide
             rw [eq]; exact CutReachable.b
  | a => rw [cycle_a]; exact CutReachable.b
  | b => rw [cycle_b]; exact CutReachable.a

theorem all_cut_rounds (n : Nat) : CutReachable (iterate n (step cutStart)) := by
  induction n with
  | zero => exact CutReachable.first
  | succ n ih => exact cut_closed ih

theorem no_cut_support {s : State} (h : CutReachable s) : pointSupported s = false := by
  cases h <;> decide

theorem no_point_after_cut_at_any_round (n : Nat) :
    pointSupported (iterate n (step cutStart)) = false := no_cut_support (all_cut_rounds n)

#print axioms cut_closed
#print axioms all_cut_rounds
#print axioms no_cut_support
#print axioms no_point_after_cut_at_any_round
#print axioms cycle_a
#print axioms cycle_b
#print axioms closed
#print axioms cycle_all_rounds
#print axioms baseline_support
#print axioms no_cycle_support
#print axioms no_support_at_any_later_round
end MixedOfferCycle
