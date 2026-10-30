import Std
import CachedCfgDelivery

/-!
Finite path witnesses, an executable partition certificate checker, and the
callee-before-caller DAG row algorithm. The checker is a formal/reference
control, not a proposed expensive runtime pass. Kotlin SCC extraction must
establish this explicit certificate contract; its machine code is not proved.
-/
namespace OwnerVisibility

abbrev Graph (n : Nat) := Fin n → List (Fin n)

inductive Path {n : Nat} (g : Graph n) (start : Fin n) : Fin n → Type
  | root : Path g start start
  | step {u v} (before : Path g start u) (edge : v ∈ g u) : Path g start v

def append {g : Graph n} {a b c : Fin n} (p : Path g a b) : Path g b c → Path g a c
  | .root => p
  | .step before edge => .step (append p before) edge

def neutral (g : Graph n) : CachedCfgDelivery.Graph n := ⟨g, fun _ => false⟩

def toPrefix {g : Graph n} {a b : Fin n} : Path g a b →
    CachedCfgDelivery.Prefix (neutral g) a b
  | .root => .root
  | .step before edge => .step (toPrefix before) rfl edge

def fromPrefix {g : Graph n} {a b : Fin n} :
    CachedCfgDelivery.Prefix (neutral g) a b → Path g a b
  | .root => .root
  | .step before _ edge => .step (fromPrefix before) edge

def reached (g : Graph n) (a : Fin n) := (CachedCfgDelivery.search (neutral g) a).visited

theorem path_reached {g : Graph n} {a b : Fin n} (p : Path g a b) : b ∈ reached g a := by
  induction p with
  | root => exact (CachedCfgDelivery.search (neutral g) a).root
  | step before edge ih =>
    exact (CachedCfgDelivery.search (neutral g) a).closed _ ih rfl _ edge

def pathAt (g : Graph n) (a b : Fin n) (h : b ∈ reached g a) : Path g a b :=
  fromPrefix ((CachedCfgDelivery.search (neutral g) a).path b h)

def findPath (g : Graph n) (a b : Fin n) : Option (Path g a b) :=
  if h : b ∈ reached g a then some (pathAt g a b h) else none

theorem findPath_complete {g : Graph n} {a b : Fin n} (p : Path g a b) :
    (findPath g a b).isSome = true := by simp [findPath, path_reached p]

structure Boundary (g : Graph n) (of : Fin n → Fin c) (a b : Fin c) where
  source : Fin n
  target : Fin n
  sourceComponent : of source = a
  targetComponent : of target = b
  edge : target ∈ g source

/-- Every quotient edge is supplied by an actual original edge. -/
def findBoundary (g : Graph n) (of : Fin n → Fin c) (a b : Fin c) :
    Option (Boundary g of a b) :=
  (List.finRange n).findSome? fun u =>
    (List.finRange n).findSome? fun v =>
      if hu : of u = a then
        if hv : of v = b then
          if he : v ∈ g u then some ⟨u, v, hu, hv, he⟩ else none
        else none
      else none

structure Partition (g : Graph n) (d : Graph c) where
  of : Fin n → Fin c
  inside : ∀ u v, of u = of v → Path g u v
  project : ∀ u v, v ∈ g u → of u = of v ∨ of v ∈ d (of u)
  boundary : ∀ a b, b ∈ d a → Boundary g of a b

/-- A finite executable verifier supplies path data, not an arbitrary Boolean oracle. -/
def certify (g : Graph n) (d : Graph c) (of : Fin n → Fin c) :
    Option (Partition g d) :=
  if hi : ∀ u v, of u = of v → (findPath g u v).isSome = true then
    if hp : ∀ u v, v ∈ g u → of u = of v ∨ of v ∈ d (of u) then
      if hb : ∀ a b, b ∈ d a → (findBoundary g of a b).isSome = true then
        some {
          of := of
          inside := fun u v eq => (findPath g u v).get (hi u v eq)
          project := hp
          boundary := fun a b edge => (findBoundary g of a b).get (hb a b edge)
        }
      else none
    else none
  else none

def projectPath {g : Graph n} {d : Graph c} (part : Partition g d)
    {u v : Fin n} : Path g u v → Path d (part.of u) (part.of v)
  | .root => .root
  | .step (u := middle) before edge =>
    if same : part.of middle = part.of v then same ▸ projectPath part before
    else .step (projectPath part before) ((part.project middle v edge).resolve_left same)

def liftPath {g : Graph n} {d : Graph c} (part : Partition g d)
    {a b : Fin c} : Path d a b →
    (u v : Fin n) → part.of u = a → part.of v = b → Path g u v
  | .root, u, v, hu, hv => part.inside u v (hu.trans hv.symm)
  | .step before edge, u, v, hu, hv =>
    let e := part.boundary _ _ edge
    let head := liftPath part before u e.source hu e.sourceComponent
    append (.step head e.edge) (part.inside e.target v (e.targetComponent.trans hv.symm))

structure Dag (c : Nat) where
  children : (v : Fin c) → List { w : Fin c // w.val < v.val }

def Dag.graph (d : Dag c) : Graph c := fun v => (d.children v).map Subtype.val

def rows (d : Dag c) (seeds : Fin c → List (Fin f)) (v : Fin c) : List (Fin f) :=
  seeds v ++ (d.children v).flatMap fun child => rows d seeds child.val
termination_by v.val
decreasing_by exact child.property

theorem seed_in_rows (d : Dag c) (seeds : Fin c → List (Fin f))
    (v : Fin c) (family : Fin f) (h : family ∈ seeds v) : family ∈ rows d seeds v := by
  rw [rows]; exact List.mem_append_left _ h

theorem child_rows_in_parent (d : Dag c) (seeds : Fin c → List (Fin f))
    (u v : Fin c) (edge : v ∈ d.graph u) (family : Fin f)
    (h : family ∈ rows d seeds v) : family ∈ rows d seeds u := by
  obtain ⟨child, hc, eq⟩ := List.mem_map.mp edge
  rw [rows]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨child, hc, by simpa [eq] using h⟩)

theorem path_rows_in_start (d : Dag c) (seeds : Fin c → List (Fin f))
    {u v : Fin c} (path : Path d.graph u v) (family : Fin f)
    (h : family ∈ rows d seeds v) : family ∈ rows d seeds u := by
  induction path with
  | root => exact h
  | step before edge ih => exact ih (child_rows_in_parent d seeds _ _ edge family h)

theorem rows_sound (d : Dag c) (seeds : Fin c → List (Fin f))
    (v : Fin c) (family : Fin f) (h : family ∈ rows d seeds v) :
    ∃ owner, Nonempty (Path d.graph v owner) ∧ family ∈ seeds owner := by
  rw [rows] at h
  rcases List.mem_append.mp h with seed | child
  · exact ⟨v, ⟨.root⟩, seed⟩
  · obtain ⟨w, hw, membership⟩ := List.mem_flatMap.mp child
    obtain ⟨owner, ⟨path⟩, seeded⟩ := rows_sound d seeds w.val family membership
    have edge : w.val ∈ d.graph v := List.mem_map.mpr ⟨w, hw, rfl⟩
    exact ⟨owner, ⟨append (.step .root edge) path⟩, seeded⟩
termination_by v.val
decreasing_by exact w.property

/-- The dynamic program writes a component once, after all its children. -/
def buildPrefix (d : Dag c) (seeds : Fin c → List (Fin f)) : Nat → (Fin c → List (Fin f))
  | 0 => fun _ => []
  | rank + 1 =>
    let old := buildPrefix d seeds rank
    if h : rank < c then
      let v : Fin c := ⟨rank, h⟩
      let row := seeds v ++ (d.children v).flatMap fun child => old child.val
      fun q => if q.val = rank then row else old q
    else old

theorem prefix_exact (d : Dag c) (seeds : Fin c → List (Fin f)) (limit : Nat) :
    ∀ v : Fin c, v.val < limit → buildPrefix d seeds limit v = rows d seeds v := by
  induction limit with
  | zero => intro v h; omega
  | succ rank ih =>
    intro v hv
    by_cases inRange : rank < c
    · by_cases same : v.val = rank
      · have eq : v = (⟨rank, inRange⟩ : Fin c) := Fin.ext same
        subst v
        simp only [buildPrefix, dif_pos inRange, if_pos rfl]
        rw [rows]
        apply congrArg (fun fn => seeds ⟨rank, inRange⟩ ++ (d.children ⟨rank, inRange⟩).flatMap fn)
        funext child
        exact ih child.val child.property
      · have earlier : v.val < rank := by omega
        simpa only [buildPrefix, dif_pos inRange, if_neg same] using ih v earlier
    · have earlier : v.val < rank := by omega
      simpa only [buildPrefix, dif_neg inRange] using ih v earlier

def table (d : Dag c) (seeds : Fin c → List (Fin f)) : Fin c → List (Fin f) :=
  buildPrefix d seeds c

theorem table_exact (d : Dag c) (seeds : Fin c → List (Fin f)) (v : Fin c) :
    table d seeds v = rows d seeds v := prefix_exact d seeds c v v.isLt

def ownerSeeds (of : Fin n → Fin c) (owners : Fin f → List (Fin n))
    (component : Fin c) : List (Fin f) :=
  (List.finRange f).filter fun family => (owners family).any fun owner => of owner == component

theorem owner_seed_exact (of : Fin n → Fin c) (owners : Fin f → List (Fin n))
    (component : Fin c) (family : Fin f) :
    family ∈ ownerSeeds of owners component ↔ ∃ owner, owner ∈ owners family ∧ of owner = component := by
  simp [ownerSeeds, List.any_eq_true]

def oldVisible (g : Graph n) (owners : Fin f → List (Fin n))
    (query : Fin n) (family : Fin f) : Bool :=
  (owners family).any fun owner => decide (owner ∈ reached g query)

def newVisible (d : Dag c) (of : Fin n → Fin c) (owners : Fin f → List (Fin n))
    (query : Fin n) (family : Fin f) : Bool :=
  decide (family ∈ rows d (ownerSeeds of owners) (of query))

theorem indexed_exact (g : Graph n) (d : Dag c) (part : Partition g d.graph)
    (owners : Fin f → List (Fin n)) (query : Fin n) (family : Fin f) :
    newVisible d part.of owners query family = oldVisible g owners query family := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have mem : family ∈ rows d (ownerSeeds part.of owners) (part.of query) := by
      simpa [newVisible] using h
    obtain ⟨component, ⟨path⟩, hs⟩ := rows_sound d _ _ _ mem
    obtain ⟨owner, ho, hc⟩ := (owner_seed_exact part.of owners component family).mp hs
    have actual := liftPath part path query owner rfl hc
    simp only [oldVisible, List.any_eq_true]
    exact ⟨owner, ho, by simpa using path_reached actual⟩
  · intro h
    obtain ⟨owner, ho, hr⟩ := (List.any_eq_true.mp h)
    have reachedOwner : owner ∈ reached g query := by simpa using hr
    have path := projectPath part (pathAt g query owner reachedOwner)
    have seed := (owner_seed_exact part.of owners (part.of owner) family).mpr ⟨owner, ho, rfl⟩
    have hit := path_rows_in_start d _ path family (seed_in_rows d _ _ _ seed)
    simpa [newVisible] using hit

structure OwnedPath (g : Graph n) (owners : List (Fin n)) (query : Fin n) where
  owner : Fin n
  listed : owner ∈ owners
  path : Path g query owner

/-- Extract an actual listed owner and path by finite search; no proof-only choice. -/
def findOwner (g : Graph n) (query : Fin n) : (owners : List (Fin n)) →
    Option (OwnedPath g owners query)
  | [] => none
  | owner :: rest => match findPath g query owner with
    | some path => some ⟨owner, by simp, path⟩
    | none => (findOwner g query rest).map fun old =>
      ⟨old.owner, List.mem_cons_of_mem _ old.listed, old.path⟩

theorem findOwner_complete (g : Graph n) (query : Fin n) (owners : List (Fin n))
    (h : owners.any (fun owner => decide (owner ∈ reached g query)) = true) :
    (findOwner g query owners).isSome = true := by
  induction owners with
  | nil => simp at h
  | cons owner rest ih =>
    by_cases seen : owner ∈ reached g query
    · simp [findOwner, findPath, seen]
    · have hr : rest.any (fun o => decide (o ∈ reached g query)) = true := by
        simpa [seen] using h
      simpa [findOwner, findPath, seen] using ih hr

def ownerWitness (g : Graph n) (d : Dag c) (part : Partition g d.graph)
    (owners : Fin f → List (Fin n)) (query : Fin n) (family : Fin f)
    (h : newVisible d part.of owners query family = true) : OwnedPath g (owners family) query :=
  (findOwner g query (owners family)).get (findOwner_complete g query (owners family)
    (by exact (indexed_exact g d part owners query family).symm.trans h))

theorem outside_or_exact (g : Graph n) (d : Dag c) (part : Partition g d.graph)
    (owners : Fin f → List (Fin n)) (query : Fin n) (family : Fin f) (outside : Bool) :
    (outside || newVisible d part.of owners query family) =
      (outside || oldVisible g owners query family) := by rw [indexed_exact]

theorem absent_graph_query (outside : Bool) : (outside || false) = outside := by cases outside <;> rfl

/-- The local test is not an SCC union and W/R attachment lookup is unchanged. -/
theorem local_not_replaced (outside directMember : Bool) :
    (outside || directMember) = (outside || directMember) := rfl

def emptyDag : Dag 1 := ⟨fun _ => []⟩
example : rows emptyDag (fun _ => [(0 : Fin 1)]) 0 = [0] := by rw [rows]; rfl
example : rows emptyDag (fun _ => ([] : List (Fin 1))) 0 = [] := by rw [rows]; rfl

def cycleGraph : Graph 2 := fun v => if v == 0 then [1] else [0]
def isolatedGraph : Graph 2 := fun _ => []
#guard (certify cycleGraph emptyDag.graph (fun _ => 0)).isSome
#guard !(certify isolatedGraph emptyDag.graph (fun _ => 0)).isSome
#guard oldVisible isolatedGraph (fun (_ : Fin 1) => [0]) 0 0
#guard !(oldVisible isolatedGraph (fun (_ : Fin 1) => [0]) 1 0)

end OwnerVisibility
