/-
  Local concrete fact trace for the DLINK counting regression after F74.

  The call cleaner is root EXACT, not a named-field action. Concrete selected
  cleaner rows are unchanged by F75. These vectors use the actual annotated
  read, binding, limit, cleaner and concrete-emission operations. They do not
  model control flow, source discovery, hand-off selection, or confirmation.
  In particular, no complete five-run iteration theorem is claimed.
-/
import ApSpec.CleanerLowering
import ApSpec.AnyTaintExDefs
import ApSpec.AbsDefs

namespace ApSpec.CurrentDemandLink
open ApSpec ApSpec.CleanerLowering ApSpec.AnyTaintEx ApSpec.Abs

/-- c's argument, its read temporary, y and m's argument have distinct bases. -/
def sourceArg : XFact := ⟨⟨⟨3, [], .any, .conc 1⟩, false⟩, Excl.empty⟩
def rootCleaner : Cleaner := ⟨8, [], .exact, some 1⟩
def sinkRequirement : PFact := ⟨8, [9, 10], .exact, .conc 1⟩
def coarseRequirement : PFact := ⟨3, [5, 6], .any, .conc 1⟩
def preciseRequirement : PFact := ⟨3, [5, 6, 9, 10], .exact, .conc 1⟩

def move (b u : Base) (p q : List Acc) : MicroEdge :=
  (⟨b, p, .star Excl.empty, .star⟩, ⟨u, q, .star Excl.empty, .star⟩)

/-- One chosen micro-edge result, followed by the actual statement/call cut. -/
def steps (e : MicroEdge) (L : Nat) (xs : List XFact) : List XFact :=
  xs.flatMap fun x => (bindX x e).facts.map (limitFX (fun _ => true) L)

def clean (xs : List XFact) : List XFact :=
  xs.flatMap fun x => (cleanResX rootCleaner x).facts

theorem precise_descendant_disjoint (b : Base) (t : Mark) (a : Acc) (r : List Acc)
    (d : Bool) :
    cleanResX ⟨b, [], .exact, some t⟩
      ⟨⟨⟨b, a :: r, .exact, .conc t⟩, d⟩, Excl.empty⟩ =
      ⟨[⟨⟨⟨b, a :: r, .exact, .conc t⟩, d⟩, Excl.empty⟩], []⟩ := by
  simp [cleanResX, cleanPosX, cleanPos, relate, dropPrefix, Nat.beq_refl]

namespace Certificate

def seed : XFact := ⟨⟨sinkRequirement, false⟩, Excl.empty⟩

/-- Backward 2: root cleaner is disjoint from p.g.h; each reversed read is cut. -/
def backward (L : Nat) : List XFact :=
  let ys := steps (move 8 7 [] []) L (clean [seed])
  let rs := steps (move 7 4 [] [6]) L ys
  steps (move 4 3 [] [5]) L rs

def coarseDemand : XFact := ⟨⟨coarseRequirement, true⟩, Excl.empty⟩
def preciseDemand : XFact := ⟨⟨preciseRequirement, false⟩, Excl.empty⟩

theorem backward_two_cut : backward 2 = [coarseDemand] := by decide
theorem backward_four_precise : backward 4 = [preciseDemand] := by decide

/-- Both are concrete-demand branches; abstract F72 emission is outside this vector. -/
def initial (d : PFact) : List XFact :=
  match emitTX emitX d sourceArg.af.fact true sourceArg.ex with
  | some (j, must, ex) => [startX j must ex]
  | none => []

def forward (L : Nat) (d : PFact) : List XFact :=
  let qs := steps (move 3 4 [5] []) L (initial d)
  let rs := steps (move 4 7 [6] []) L qs
  clean (steps (move 7 8 [] []) L rs)

def broadLink : XFact := ⟨⟨⟨8, [], .any, .conc 1⟩, true⟩, Excl.empty⟩
def preciseLink : XFact := ⟨⟨sinkRequirement, false⟩, Excl.empty⟩

theorem coarse_initial_must :
    initial coarseRequirement = [⟨⟨coarseRequirement, false⟩, Excl.empty⟩] := by decide

theorem run_three_demand_link : forward 3 coarseRequirement = [broadLink] := by decide

/-- A demand link can emit an exact premise whose start and sink edge are normal. -/
theorem run_three_normal_start :
    emitW sinkRequirement broadLink.af.fact = some sinkRequirement ∧
      startX sinkRequirement false Excl.empty = seed := by decide

theorem run_five_normal_link : forward 5 preciseRequirement = [preciseLink] := by decide

def check : Bool := backward 2 == [coarseDemand] && backward 4 == [preciseDemand] &&
  forward 3 coarseRequirement == [broadLink] &&
  emitW sinkRequirement broadLink.af.fact == some sinkRequirement &&
  startX sinkRequirement false Excl.empty == seed &&
  forward 5 preciseRequirement == [preciseLink]

theorem checked : check = true := by decide

end Certificate
end ApSpec.CurrentDemandLink
