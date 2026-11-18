import HeadSafety
namespace HeadNeutralPlan
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline NormalUniformNE NestedSavedReplayCycle NestedColdMachine
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def baseFamily (run limit : Nat) (backward : Bool) (row : Row) (a : Offered) : List Seed :=
  let ordinary := HeadPolicy.emit run limit backward row.entry a
  if ordinary.isEmpty && a.ap.tail == .star &&
      (row.entry.tail == .may || row.entry.tail == .ne) &&
      (dropHead a.ap.path row.entry.path).isSome && a.ap.path != row.entry.path then
    HeadPolicy.emit run limit backward row.entry {a with ap := {a.ap with path := row.entry.path,tail := .may}}
  else ordinary

def fields (rows : List Row) (normals : List (Edge × Bool)) (row : Row) : List Nat :=
  let heads := (rows.filter fun r => decide (r.exit = row.exit)).map (·.entry.path) ++
    ((normals.filter fun r => !r.1.2.demand).map (·.1.1.path))
  (heads.filterMap fun h => match dropHead row.entry.path h with
    | some (f :: _) => some f | _ => none).eraseDups

def compatibleChild (a : Offered) (path : Path) : Bool :=
  ((dropHead a.ap.path path).isSome || (dropHead path a.ap.path).isSome) &&
    (a.ap.tail != .exact || a.ap.path == path)

def plan (run limit : Nat) (backward : Bool) (rows : List Row)
    (normals : List (Edge × Bool)) (row : Row) (a : Offered) : List (Seed × List Nat) :=
  let next := fields rows normals row
  let qs := baseFamily run limit backward row a
  unique (fun q => apKey q.1.ap) (qs.flatMap fun q =>
    if q.ap.tail == .star && q.ap.path == row.entry.path &&
        (row.entry.tail == .may || row.entry.tail == .ne) then
      let chosen := next.filter fun f =>
        decide (q.ap.path.length+1 ≤ min limit (row.entry.path.length+1)) &&
        compatibleChild a (q.ap.path ++ [f])
      [(q,chosen)] ++ chosen.flatMap (fun f =>
        [(⟨{q.ap with path := q.ap.path ++ [f],tail := .exact},false⟩,[]),
         (⟨{q.ap with path := q.ap.path ++ [f]},false⟩,[])])
    else [(q,[])])

abbrev Cell := Row × List (Seed × List Nat)
def cells (run limit : Nat) (backward : Bool) (rows : List Row)
    (normals : List (Edge × Bool)) (domain : List Offered) : List Cell :=
  if run == 1 then
    if domain.isEmpty then [] else [(⟨point p [] .may,point ret [] .star⟩,[(⟨point p [] .star,false⟩,[])])]
  else rows.flatMap fun row => domain.map fun a => (row,plan run limit backward rows normals row a)


theorem baseFamily_eq_old (run k : Nat) (back : Bool) (row : Row) (a : Offered)
    (abstract : row.entry.mark = none) :
    baseFamily run k back row a = NestedColdMachine.baseFamily run k back row a := by
  simp [baseFamily,NestedColdMachine.baseFamily,HeadPolicy.abstract_demands_are_exactly_the_old_policy,
    abstract]

theorem plan_eq_old (run k : Nat) (back : Bool) (rows : List Row)
    (normals : List (Edge × Bool)) (row : Row) (a : Offered)
    (abstract : row.entry.mark = none) :
    plan run k back rows normals row a = NestedColdMachine.plan run k back rows normals row a := by
  simp only [plan,NestedColdMachine.plan,baseFamily_eq_old run k back row a abstract]
  rfl

def FlowRows (rows : List Row) : Prop := ∀ row ∈ rows, row.entry.mark = none

theorem plan_list_eq_old (run k : Nat) (back : Bool) (rows : List Row)
    (normals : List (Edge × Bool)) (a : Offered) (abstract : FlowRows rows) :
    rows.map (fun row => plan run k back rows normals row a) =
      rows.map (fun row => NestedColdMachine.plan run k back rows normals row a) := by
  apply List.map_congr_left
  intro row inside
  exact plan_eq_old run k back rows normals row a (abstract row inside)

theorem cells_eq_old (run k : Nat) (back : Bool) (rows : List Row)
    (normals : List (Edge × Bool)) (as : List Offered) (abstract : FlowRows rows) :
    cells run k back rows normals as = NestedColdMachine.cells run k back rows normals as := by
  unfold cells NestedColdMachine.cells
  split
  · rfl
  · have same : ∀ row ∈ rows,
        as.map (fun a => (row,plan run k back rows normals row a)) =
          as.map (fun a => (row,NestedColdMachine.plan run k back rows normals row a)) := by
      intro row inside
      simp only [plan_eq_old run k back rows normals row _ (abstract row inside)]
    have general {α β : Type} (xs : List α) (f g : α → List β)
        (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
      induction xs with
      | nil => rfl
      | cons x xs ih =>
          rw [List.flatMap_cons,List.flatMap_cons,h x (by simp)]
          rw [ih (fun a ha => h a (by simp [ha]))]
    exact general rows _ _ same
end HeadNeutralPlan
