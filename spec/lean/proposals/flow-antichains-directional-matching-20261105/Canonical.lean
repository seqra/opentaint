import Std

namespace FlowAntichains.Canonical

abbrev Path := List Nat

/-- MAY and MUST are distinct headers; no new cross-tail rule is selected. -/
inductive Tail where
  | may | must
  deriving DecidableEq, Repr

/-- `scope` is the exact complete method/P/direction/entry/exit/base/layer/kind key.
`atom` and `protected` describe one ordinary or protected mask membership.
Flow mx is interpreted pointwise at an arbitrary mark atom; this implies
no native mark enumeration or finite-positive FLOW output channel.
Field exclusions stay explicit. Equality never forgets a header component. -/
structure Header where
  scope : Nat
  tail : Tail
  excluded : List Nat
  atom : Nat
  protectedBit : Bool
  deriving DecidableEq, Repr

structure Row where
  header : Header
  path : Path
  deriving DecidableEq, Repr

/-- Executable scalar same-header MAY/MUST coverage. An exclusion tests only
 the first strict descendant accessor, exactly as the native scalar reference. -/
def pathCovers (tail : Tail) (excluded : List Nat) : Path → Path → Bool
  | [], [] => true
  | [], field :: _ => match tail with
    | .may => true
    | .must => decide (field ∉ excluded)
  | _ :: _, [] => false
  | field :: rest, other :: suffix =>
      if field = other then pathCovers tail excluded rest suffix else false

def covers (a b : Row) : Bool :=
  decide (a.header = b.header) && pathCovers a.header.tail a.header.excluded a.path b.path

theorem pathCovers_refl (tail : Tail) (excluded : List Nat) (p : Path) :
    pathCovers tail excluded p p = true := by
  induction p with
  | nil => rfl
  | cons x xs ih => simpa [pathCovers] using ih

theorem pathCovers_trans (tail : Tail) (excluded : List Nat) (a b c : Path)
    (ab : pathCovers tail excluded a b = true)
    (bc : pathCovers tail excluded b c = true) :
    pathCovers tail excluded a c = true := by
  induction a generalizing b c with
  | nil =>
    cases b with
    | nil => exact bc
    | cons x xs =>
      cases c with
      | nil => simp [pathCovers] at bc
      | cons y ys =>
        by_cases same : x = y
        · subst y; simpa [pathCovers] using ab
        · simp [pathCovers, same] at bc
  | cons x xs ih =>
    cases b with
    | nil => simp [pathCovers] at ab
    | cons y ys =>
      by_cases same : x = y
      · subst y
        cases c with
        | nil => simp [pathCovers] at bc
        | cons z zs =>
          by_cases other : x = z
          · subst z
            simpa [pathCovers] using ih ys zs (by simpa [pathCovers] using ab)
              (by simpa [pathCovers] using bc)
          · simp [pathCovers, other] at bc
      · simp [pathCovers, same] at ab

theorem pathCovers_antisymm (tail : Tail) (excluded : List Nat) (a b : Path)
    (ab : pathCovers tail excluded a b = true)
    (ba : pathCovers tail excluded b a = true) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons x xs => simp [pathCovers] at ba
  | cons x xs ih =>
    cases b with
    | nil => simp [pathCovers] at ab
    | cons y ys =>
      by_cases same : x = y
      · subst y
        have rest := ih ys (by simpa [pathCovers] using ab)
          (by simpa [pathCovers] using ba)
        simp [rest]
      · simp [pathCovers, same] at ab

theorem covers_refl (a : Row) : covers a a = true := by
  simp [covers, pathCovers_refl]

theorem covers_header (a b : Row) (h : covers a b = true) : a.header = b.header := by
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem covers_trans (a b c : Row) (ab : covers a b = true) (bc : covers b c = true) :
    covers a c = true := by
  have ha := covers_header a b ab
  have hb := covers_header b c bc
  apply Bool.and_eq_true_iff.mpr
  constructor
  · exact decide_eq_true (ha.trans hb)
  · have abp := (Bool.and_eq_true_iff.mp ab).2
    have bcp := (Bool.and_eq_true_iff.mp bc).2
    rw [← ha] at bcp
    exact pathCovers_trans _ _ _ _ _ abp bcp

theorem covers_antisymm (a b : Row) (ab : covers a b = true) (ba : covers b a = true) : a = b := by
  have hh := covers_header a b ab
  have abp := (Bool.and_eq_true_iff.mp ab).2
  have bap := (Bool.and_eq_true_iff.mp ba).2
  rw [← hh] at bap
  have hp := pathCovers_antisymm _ _ _ _ abp bap
  cases a; cases b
  simp_all

/-- The reference denotation: all scalar memberships covered by some stored row. -/
def denotes (rows : List Row) (query : Row) : Prop :=
  ∃ row, row ∈ rows ∧ covers row query = true

def covered (rows : List Row) (query : Row) : Bool :=
  rows.any (fun row => covers row query)

theorem covered_iff (rows : List Row) (query : Row) :
    covered rows query = true ↔ denotes rows query := by
  simp [covered, denotes, List.any_eq_true]

/-- Insert a genuinely new row, then remove older rows that it covers.
A covered incoming row has no effect. This handles both arrival orders. -/
def insert (rows : List Row) (row : Row) : List Row :=
  if covered rows row then rows
  else row :: rows.filter (fun old => !(covers row old))

/-- One executable kernel is used inside a packed packet and across old packets. -/
def normalize : List Row → List Row
  | [] => []
  | row :: rest => insert (normalize rest) row

/-- Constructive witnesses: every emitted row is an original scalar membership. -/
theorem insert_subset (rows : List Row) (row : Row) (x : Row) :
    x ∈ insert rows row → x = row ∨ x ∈ rows := by
  unfold insert
  split
  · intro hx; exact Or.inr hx
  · intro hx
    rcases List.mem_cons.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_filter.mp h).1

theorem insert_denotes (rows : List Row) (row query : Row) :
    denotes (insert rows row) query ↔ denotes rows query ∨ covers row query = true := by
  unfold insert
  split
  next h =>
    constructor
    · intro hq; exact Or.inl hq
    · intro hq
      rcases hq with hq | hq
      · exact hq
      · rcases (covered_iff rows row).mp h with ⟨old, hold, hcover⟩
        exact ⟨old, hold, covers_trans old row query hcover hq⟩
  next h =>
    constructor
    · rintro ⟨x, hx, hq⟩
      rcases List.mem_cons.mp hx with hx | hx
      · subst x; exact Or.inr hq
      · exact Or.inl ⟨x, (List.mem_filter.mp hx).1, hq⟩
    · intro hq
      rcases hq with ⟨x, hx, hcover⟩ | hcover
      · by_cases removed : covers row x = true
        · exact ⟨row, by simp, covers_trans row x query removed hcover⟩
        · exact ⟨x, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hx, by simpa using removed⟩), hcover⟩
      · exact ⟨row, by simp, hcover⟩

theorem normalize_subset (rows : List Row) (row : Row) : row ∈ normalize rows → row ∈ rows := by
  induction rows with
  | nil => simp [normalize]
  | cons x xs ih =>
    intro h
    rcases insert_subset (normalize xs) x row h with h | h
    · subst row; simp
    · exact List.mem_cons_of_mem _ (ih h)

theorem normalize_denotes (rows : List Row) (query : Row) :
    denotes (normalize rows) query ↔ denotes rows query := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    change denotes (insert (normalize rest) row) query ↔ denotes (row :: rest) query
    rw [insert_denotes, ih]
    unfold denotes
    simp only [List.mem_cons]
    constructor
    · rintro (⟨x, hx, h⟩ | h)
      · exact ⟨x, Or.inr hx, h⟩
      · exact ⟨row, Or.inl rfl, h⟩
    · rintro ⟨x, (hx | hx), h⟩
      · subst x; exact Or.inr h
      · exact Or.inl ⟨x, hx, h⟩

def Reduced (rows : List Row) : Prop :=
  ∀ a, a ∈ rows → ∀ b, b ∈ rows → a ≠ b → covers a b = false

theorem no_member_covers (rows : List Row) (row x : Row)
    (h : covered rows row = false) (hx : x ∈ rows) : covers x row = false := by
  by_cases hc : covers x row = true
  · have yes : covered rows row = true := (covered_iff rows row).mpr ⟨x, hx, hc⟩
    simp [h] at yes
  · exact Bool.eq_false_iff.mpr hc

theorem insert_reduced (rows : List Row) (row : Row) (hr : Reduced rows) :
    Reduced (insert rows row) := by
  unfold insert
  split
  · exact hr
  next h =>
    have hn : covered rows row = false := by simpa using h
    intro a ha b hb hab
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      rcases List.mem_cons.mp hb with hb | hb
      · subst b; exact False.elim (hab rfl)
      · simpa using (List.mem_filter.mp hb).2
    · rcases List.mem_cons.mp hb with hb | hb
      · subst b; exact no_member_covers rows row a hn (List.mem_filter.mp ha).1
      · exact hr a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1 hab

theorem normalize_reduced (rows : List Row) : Reduced (normalize rows) := by
  induction rows with
  | nil => intro a ha; simp [normalize] at ha
  | cons row rest ih => exact insert_reduced _ _ ih

/-- Repeated normalization keeps exactly the same spatial denotation. -/
theorem normalize_idempotent_denotation (rows : List Row) (q : Row) :
    denotes (normalize (normalize rows)) q ↔ denotes (normalize rows) q :=
  normalize_denotes _ _

/-- There is no crossing of complete P/ports/layer/tail/mask/protection keys. -/
theorem different_header_never_covers (a b : Row) (h : a.header ≠ b.header) :
    covers a b = false := by simp [covers, h]

/-- Exclusions are real, not an omitted normalizer guard. -/
theorem excluded_first_field_not_covered (scope atom field : Nat) (rest : Path) :
    let h : Header := ⟨scope, .must, [field], atom, false⟩
    covers ⟨h, []⟩ ⟨h, field :: rest⟩ = false := by simp [covers, pathCovers]

theorem may_prefix_covers (h : Header) (p r : Path) (ht : h.tail = .may) :
    covers ⟨h,p⟩ ⟨h,p ++ r⟩ = true := by
  induction p with
  | nil => cases r <;> simp [covers, pathCovers, ht]
  | cons f fs ih => simpa [covers, pathCovers] using ih

/-- A protected dependency is a separate mask stream. Ordinary data cannot erase it. -/
theorem plain_cannot_cover_protected (h : Header) (p q : Path) :
    covers ⟨{ h with protectedBit := false }, p⟩ ⟨{ h with protectedBit := true }, q⟩ = false := by
  simp [covers]

/-- Complete keys exclude field E, which is a per-region set. The opaque scope
encodes the full P/ports/layer/base/direction/kind tuple without projection. -/
structure RegionKey where
  scope : Nat
  tail : Tail
  atom : Nat
  protectedBit : Bool
  deriving DecidableEq, Repr

structure Region where
  key : RegionKey
  path : Path
  excluded : List Nat
  deriving DecidableEq, Repr

/-- Point membership is executable. A rooted region always includes its anchor;
only the first strict descendant accessor is tested against E. -/
def atPoint (r : Region) (location : Path) : Bool :=
  pathCovers r.key.tail r.excluded r.path location

def unionAt (rows : List Region) (key : RegionKey) (location : Path) : Bool :=
  rows.any (fun r => decide (r.key = key) && atPoint r location)

def meetExclusions (a b : List Nat) : List Nat :=
  a.filter (fun f => decide (f ∈ b))

def fillExclusion (a : List Nat) (field : Nat) : List Nat :=
  a.filter (fun f => decide (f ≠ field))

theorem meet_membership (a b : List Nat) (f : Nat) :
    f ∈ meetExclusions a b ↔ f ∈ a ∧ f ∈ b := by simp [meetExclusions]

theorem fill_membership (a : List Nat) (f g : Nat) :
    g ∈ fillExclusion a f ↔ g ∈ a ∧ g ≠ f := by simp [fillExclusion]

theorem same_anchor_union (tail : Tail) (a b : List Nat) (location : Path) :
    pathCovers tail (meetExclusions a b) [] location =
      (pathCovers tail a [] location || pathCovers tail b [] location) := by
  cases location with
  | nil => rfl
  | cons f rest =>
    by_cases ha : f ∈ a <;> by_cases hb : f ∈ b <;>
      cases tail <;> simp [pathCovers, meet_membership, ha, hb]

theorem complete_root (tail : Tail) (location : Path) :
    pathCovers tail [] [] location = true := by
  cases location <;> cases tail <;> simp [pathCovers]

theorem direct_child_fill (tail : Tail) (a : List Nat) (f : Nat) (location : Path) :
    pathCovers tail (fillExclusion a f) [] location =
      (pathCovers tail a [] location || pathCovers tail [] [f] location) := by
  cases location with
  | nil => rfl
  | cons g rest =>
    by_cases same : g = f
    · subst g
      cases tail <;> simp [pathCovers, fill_membership, complete_root]
    · have other : f ≠ g := Ne.symm same
      cases tail <;> simp [pathCovers, fill_membership, same, other]

/-- An admitted strict descendant is covered regardless of its own E. -/
theorem admitted_descendant (tail : Tail) (a b : List Nat) (f : Nat)
    (rest location : Path)
    (admitted : tail = .may ∨ f ∉ a)
    (inside : pathCovers tail b (f :: rest) location = true) :
    pathCovers tail a [] location = true := by
  cases location with
  | nil => simp [pathCovers] at inside
  | cons g suffix =>
    by_cases same : f = g
    · subst g
      rcases admitted with h | h
      · simp [pathCovers, h]
      · cases tail <;> simp [pathCovers, h]
    · simp [pathCovers, same] at inside

theorem descendant_union (tail : Tail) (a b : List Nat) (f : Nat)
    (rest location : Path) (admitted : tail = .may ∨ f ∉ a) :
    pathCovers tail a [] location =
      (pathCovers tail a [] location || pathCovers tail b (f :: rest) location) := by
  cases h : pathCovers tail b (f :: rest) location with
  | false => simp
  | true => simp [admitted_descendant tail a b f rest location admitted h]

/-- Merge one pair by the selected laws. Both orderings work. A missing direct
complete child is never guessed. Equal paths join E by intersection. -/
def mergePaths (tail : Tail) (aE bE : List Nat) : Path → Path → Option (Path × List Nat)
  | [], [] => some ([], meetExclusions aE bE)
  | [], f :: rest =>
      if tail = .may ∨ f ∉ aE then some ([], aE)
      else if rest = [] ∧ bE = [] then some ([], fillExclusion aE f) else none
  | f :: rest, [] =>
      if tail = .may ∨ f ∉ bE then some ([], bE)
      else if rest = [] ∧ aE = [] then some ([], fillExclusion bE f) else none
  | f :: rest, g :: suffix =>
      if f = g then (mergePaths tail aE bE rest suffix).map (fun p => (f :: p.1, p.2))
      else none

/-- Every successful executable pair rewrite preserves the exact union of all
concrete locations, including the formerly excluded child's anchor. -/
theorem mergePaths_exact (tail : Tail) (aE bE : List Nat) (a b out : Path)
    (outE : List Nat) (h : mergePaths tail aE bE a b = some (out,outE))
    (location : Path) :
    pathCovers tail outE out location =
      (pathCovers tail aE a location || pathCovers tail bE b location) := by
  induction a generalizing b out location with
  | nil =>
    cases b with
    | nil =>
      simp [mergePaths] at h
      rcases h with ⟨rfl, rfl⟩
      exact same_anchor_union tail aE bE location
    | cons f rest =>
      unfold mergePaths at h
      split at h
      next admitted =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact descendant_union tail aE bE f rest location admitted
      next notAdmitted =>
        split at h
        next complete =>
          rcases complete with ⟨rfl,rfl⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl,rfl⟩
          exact direct_child_fill tail aE f location
        next _ => simp at h
  | cons f rest ih =>
    cases b with
    | nil =>
      unfold mergePaths at h
      split at h
      next admitted =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        simpa [Bool.or_comm] using descendant_union tail bE aE f rest location admitted
      next notAdmitted =>
        split at h
        next complete =>
          rcases complete with ⟨rfl,rfl⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl,rfl⟩
          simpa [Bool.or_comm] using direct_child_fill tail bE f location
        next _ => simp at h
    | cons g suffix =>
      unfold mergePaths at h
      split at h
      next same =>
        subst g
        cases hm : mergePaths tail aE bE rest suffix with
        | none => simp [hm] at h
        | some pair =>
          rcases pair with ⟨p,e⟩
          simp [hm] at h
          rcases h with ⟨rfl,rfl⟩
          cases location with
          | nil => rfl
          | cons x xs =>
            by_cases he : f = x
            · subst x
              simpa [pathCovers] using ih suffix p hm xs
            · simp [pathCovers, he]
      next different => simp at h

def mergeRegions (a b : Region) : Option Region :=
  if a.key = b.key then
    (mergePaths a.key.tail a.excluded b.excluded a.path b.path).map
      (fun p => ⟨a.key, p.1, p.2⟩)
  else none

theorem mergeRegions_key (a b out : Region) (h : mergeRegions a b = some out) :
    a.key = b.key ∧ out.key = a.key := by
  unfold mergeRegions at h
  split at h
  next same =>
    cases hm : mergePaths a.key.tail a.excluded b.excluded a.path b.path with
    | none => simp [hm] at h
    | some pair => simp [hm] at h; subst out; exact ⟨same,rfl⟩
  next different => simp at h

theorem mergeRegions_exact (a b out : Region) (h : mergeRegions a b = some out)
    (key : RegionKey) (location : Path) :
    unionAt [out] key location = unionAt [a,b] key location := by
  have ⟨same, outKey⟩ := mergeRegions_key a b out h
  unfold mergeRegions at h
  rw [if_pos same] at h
  cases hm : mergePaths a.key.tail a.excluded b.excluded a.path b.path with
  | none => simp [hm] at h
  | some pair =>
    rcases pair with ⟨p,e⟩
    simp [hm] at h
    subst out
    by_cases hk : a.key = key
    · subst key
      simp only [unionAt, List.any_cons, List.any_nil, decide_true, Bool.true_and,
        Bool.or_false, atPoint]
      rw [← same]
      simpa using mergePaths_exact _ _ _ _ _ _ _ hm location
    · simp [unionAt, hk, ← same]

/-- A single candidate scan returns an executable witness: the joined row and
all non-selected rows, in their old relative order. -/
def mergeWith (row : Region) : List Region → Option (Region × List Region)
  | [] => none
  | old :: rest =>
    match mergeRegions row old with
    | some joined => some (joined,rest)
    | none => (mergeWith row rest).map (fun p => (p.1, old :: p.2))

theorem mergeWith_exact (row : Region) (rows rest : List Region) (joined : Region)
    (h : mergeWith row rows = some (joined,rest)) (key : RegionKey) (location : Path) :
    unionAt (joined :: rest) key location = unionAt (row :: rows) key location := by
  induction rows generalizing rest joined with
  | nil => simp [mergeWith] at h
  | cons old tail ih =>
    cases hm : mergeRegions row old with
    | some value =>
      simp [mergeWith, hm] at h
      rcases h with ⟨rfl,rfl⟩
      have pair := mergeRegions_exact row old value hm key location
      simpa [unionAt, Bool.or_assoc] using congrArg
        (fun x => x || unionAt tail key location) pair
    | none =>
      cases hr : mergeWith row tail with
      | none => simp [mergeWith,hm,hr] at h
      | some result =>
        rcases result with ⟨value,remaining⟩
        simp [mergeWith,hm,hr] at h
        rcases h with ⟨rfl,rfl⟩
        have eq := ih remaining value hr
        simp only [unionAt, List.any_cons] at eq ⊢
        simpa [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm] using
          congrArg (fun x => (decide (old.key = key) && atPoint old location) || x) eq

def mergeOne : List Region → Option (List Region)
  | [] => none
  | row :: rest =>
    match mergeWith row rest with
    | some p => some (p.1 :: p.2)
    | none => (mergeOne rest).map (fun rows => row :: rows)

theorem mergeOne_exact (rows out : List Region) (h : mergeOne rows = some out)
    (key : RegionKey) (location : Path) : unionAt out key location = unionAt rows key location := by
  induction rows generalizing out with
  | nil => simp [mergeOne] at h
  | cons row rest ih =>
    cases hm : mergeWith row rest with
    | some pair =>
      rcases pair with ⟨joined, remaining⟩
      simp [mergeOne,hm] at h
      subst out
      exact mergeWith_exact row rest remaining joined hm key location
    | none =>
      cases hr : mergeOne rest with
      | none => simp [mergeOne,hm,hr] at h
      | some value =>
        simp [mergeOne,hm,hr] at h
        subst out
        have eq := ih value hr
        simp only [unionAt, List.any_cons]
        exact congrArg (fun b => (decide (row.key = key) && atPoint row location) || b) eq

/-- The list reference rescans after every merge. That permits bottom-up hole
fill and both arrival orders. At most n-1 successful rewrites can occur. -/
def normalizeRegionsFuel : Nat → List Region → List Region
  | 0, rows => rows
  | fuel + 1, rows =>
    match mergeOne rows with
    | none => rows
    | some out => normalizeRegionsFuel fuel out

def normalizeRegions (rows : List Region) : List Region :=
  normalizeRegionsFuel rows.length rows

theorem normalizeRegionsFuel_exact (fuel : Nat) (rows : List Region)
    (key : RegionKey) (location : Path) :
    unionAt (normalizeRegionsFuel fuel rows) key location = unionAt rows key location := by
  induction fuel generalizing rows with
  | zero => rfl
  | succ fuel ih =>
    unfold normalizeRegionsFuel
    cases h : mergeOne rows with
    | none => rfl
    | some out => rw [ih, mergeOne_exact rows out h key location]

theorem normalizeRegions_exact (rows : List Region) (key : RegionKey) (location : Path) :
    unionAt (normalizeRegions rows) key location = unionAt rows key location :=
  normalizeRegionsFuel_exact _ _ _ _

theorem unequal_keys_never_join (a b : Region) (h : a.key ≠ b.key) :
    mergeRegions a b = none := by simp [mergeRegions,h]

/-- This is the user's selected cross-E law. The descendant's E may be nonempty. -/
theorem cross_E_must_cover (e childE : List Nat) (field : Nat) (rest : Path)
    (h : field ∉ e) : mergePaths .must e childE [] (field :: rest) = some ([],e) := by
  simp [mergePaths,h]

theorem complete_direct_child_fills (e : List Nat) (field : Nat) (h : field ∈ e) :
    mergePaths .must e [] [] [field] = some ([],fillExclusion e field) := by
  simp [mergePaths,h]

theorem longer_child_does_not_fill (field next : Nat) :
    mergePaths .must [field] [] [] [field,next] = none := by simp [mergePaths]

theorem excluded_child_does_not_fill (field next : Nat) :
    mergePaths .must [field] [next] [] [field] = none := by simp [mergePaths]

/-- Negative witnesses are concrete locations, not an appeal to a classical
counterexample: the child's root is missing in the long-child case. -/
theorem longer_child_missing_anchor (field next : Nat) :
    (pathCovers .must [field] [] [field] || pathCovers .must [] [field,next] [field]) = false := by
  simp [pathCovers]

theorem excluded_child_missing_descendant (field next : Nat) :
    (pathCovers .must [field] [] [field,next] || pathCovers .must [next] [field] [field,next]) = false := by
  simp [pathCovers]

theorem mergeWith_length (row : Region) (rows rest : List Region) (joined : Region)
    (h : mergeWith row rows = some (joined,rest)) : rest.length + 1 = rows.length := by
  induction rows generalizing rest joined with
  | nil => simp [mergeWith] at h
  | cons old tail ih =>
    cases hm : mergeRegions row old with
    | some value =>
      simp [mergeWith,hm] at h
      rcases h with ⟨rfl,rfl⟩
      simp
    | none =>
      cases hr : mergeWith row tail with
      | none => simp [mergeWith,hm,hr] at h
      | some pair =>
        rcases pair with ⟨value,remaining⟩
        simp [mergeWith,hm,hr] at h
        rcases h with ⟨rfl,rfl⟩
        have eq := ih remaining value hr
        simp only [List.length_cons]
        omega

theorem mergeOne_length (rows out : List Region) (h : mergeOne rows = some out) :
    out.length + 1 = rows.length := by
  induction rows generalizing out with
  | nil => simp [mergeOne] at h
  | cons row rest ih =>
    cases hm : mergeWith row rest with
    | some pair =>
      rcases pair with ⟨joined,remaining⟩
      simp [mergeOne,hm] at h
      subst out
      have eq := mergeWith_length row rest remaining joined hm
      simp only [List.length_cons]
      omega
    | none =>
      cases hr : mergeOne rest with
      | none => simp [mergeOne,hm,hr] at h
      | some value =>
        simp [mergeOne,hm,hr] at h
        subst out
        have eq := ih value hr
        simp only [List.length_cons]
        omega

theorem normalizeRegionsFuel_irreducible (fuel : Nat) (rows : List Region)
    (enough : rows.length ≤ fuel) : mergeOne (normalizeRegionsFuel fuel rows) = none := by
  induction fuel generalizing rows with
  | zero =>
    cases rows with
    | nil => rfl
    | cons row rest => simp at enough
  | succ fuel ih =>
    unfold normalizeRegionsFuel
    cases h : mergeOne rows with
    | none => exact h
    | some out =>
      have eq := mergeOne_length rows out h
      exact ih out (by omega)

theorem normalizeRegions_irreducible (rows : List Region) :
    mergeOne (normalizeRegions rows) = none :=
  normalizeRegionsFuel_irreducible _ _ (Nat.le_refl _)

theorem normalizeRegionsFuel_stable (fuel : Nat) (rows : List Region)
    (h : mergeOne rows = none) : normalizeRegionsFuel fuel rows = rows := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [normalizeRegionsFuel,h]

theorem normalizeRegions_idempotent (rows : List Region) :
    normalizeRegions (normalizeRegions rows) = normalizeRegions rows := by
  exact normalizeRegionsFuel_stable _ _ (normalizeRegions_irreducible rows)

/-- Executable header index: only candidates in the exact complete key bucket
are sent to the spatial kernel. The production trie may further index paths. -/
def headerBucket (key : RegionKey) (rows : List Region) : List Region :=
  rows.filter (fun row => decide (row.key = key))

theorem headerBucket_union (key : RegionKey) (rows : List Region) (location : Path) :
    unionAt (headerBucket key rows) key location = unionAt rows key location := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    by_cases same : row.key = key
    · simp_all [headerBucket,unionAt]
    · simp_all [headerBucket,unionAt]

def indexedNormalize (key : RegionKey) (rows : List Region) : List Region :=
  normalizeRegions (headerBucket key rows)

theorem indexed_reference_equivalent (key : RegionKey) (rows : List Region) (location : Path) :
    unionAt (indexedNormalize key rows) key location = unionAt (normalizeRegions rows) key location := by
  rw [indexedNormalize,normalizeRegions_exact,headerBucket_union,normalizeRegions_exact]

/-- Cost is the number of candidate headers sent to a per-key scalar pass.
Index construction and native DAG operations are explicitly outside this count. -/
def indexedCandidateTests (key : RegionKey) (rows : List Region) : Nat :=
  (headerBucket key rows).length

theorem indexed_candidate_bound (key : RegionKey) (rows : List Region) :
    indexedCandidateTests key rows ≤ rows.length := by
  exact List.length_filter_le _ _

theorem unrelated_headers_cost_zero (key : RegionKey) (rows : List Region)
    (allOther : ∀ row ∈ rows, row.key ≠ key) : indexedCandidateTests key rows = 0 := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have other := allOther row (by simp)
    have remaining : ∀ value ∈ rest, value.key ≠ key := by
      intro value mem
      exact allOther value (by simp [mem])
    have eq : headerBucket key (row :: rest) = headerBucket key rest := by
      simp only [headerBucket, List.filter_cons, other, decide_false, Bool.false_eq_true, if_false]
    unfold indexedCandidateTests
    rw [eq]
    exact ih remaining

/-- Shared DAG node identity alone is insufficient for memoization: the same
leaf below two fields observes different inherited exclusion coverage. -/
theorem inherited_context_matters (excluded other : Nat) (different : excluded ≠ other) :
    pathCovers .must [excluded] [] [excluded] = false ∧
    pathCovers .must [excluded] [] [other] = true := by
  simp [pathCovers,Ne.symm different]

/-- A constructive overlap witness. The common anchor is legal even with
incomparable exclusions. At unequal comparable prefixes the shorter region's
first-field exclusion decides overlap; the deeper anchor is the witness. -/
def overlapWitness (aTail bTail : Tail) (aE bE : List Nat) : Path → Path → Option Path
  | [], [] => some []
  | [], f :: rest =>
      if aTail = .may ∨ f ∉ aE then some (f :: rest) else none
  | f :: rest, [] =>
      if bTail = .may ∨ f ∉ bE then some (f :: rest) else none
  | f :: rest, g :: suffix =>
      if f = g then (overlapWitness aTail bTail aE bE rest suffix).map (f :: ·) else none

theorem overlapWitness_sound (aTail bTail : Tail) (aE bE : List Nat)
    (a b witness : Path) (h : overlapWitness aTail bTail aE bE a b = some witness) :
    pathCovers aTail aE a witness = true ∧ pathCovers bTail bE b witness = true := by
  induction a generalizing b witness with
  | nil =>
    cases b with
    | nil => simp [overlapWitness] at h; subst witness; exact ⟨rfl,rfl⟩
    | cons f rest =>
      unfold overlapWitness at h
      split at h
      next admitted =>
        simp at h
        subst witness
        constructor
        · rcases admitted with eq | notIn
          · simp [pathCovers,eq]
          · cases aTail <;> simp [pathCovers,notIn]
        · exact pathCovers_refl _ _ _
      next _ => simp at h
  | cons f rest ih =>
    cases b with
    | nil =>
      unfold overlapWitness at h
      split at h
      next admitted =>
        simp at h
        subst witness
        constructor
        · exact pathCovers_refl _ _ _
        · rcases admitted with eq | notIn
          · simp [pathCovers,eq]
          · cases bTail <;> simp [pathCovers,notIn]
      next _ => simp at h
    | cons g suffix =>
      unfold overlapWitness at h
      split at h
      next same =>
        subst g
        cases hm : overlapWitness aTail bTail aE bE rest suffix with
        | none => simp [hm] at h
        | some tail =>
          simp [hm] at h
          subst witness
          have ⟨ha,hb⟩ := ih suffix tail hm
          simpa [pathCovers] using And.intro ha hb
      next _ => simp at h

theorem overlapWitness_complete (aTail bTail : Tail) (aE bE : List Nat)
    (a b location : Path)
    (ha : pathCovers aTail aE a location = true)
    (hb : pathCovers bTail bE b location = true) :
    (overlapWitness aTail bTail aE bE a b).isSome = true := by
  induction a generalizing b location with
  | nil =>
    cases b with
    | nil => rfl
    | cons f rest =>
      have admitted : aTail = .may ∨ f ∉ aE := by
        cases location with
        | nil => simp [pathCovers] at hb
        | cons g suffix =>
          by_cases same : f = g
          · subst g
            cases aTail with
            | may => exact Or.inl rfl
            | must => exact Or.inr (of_decide_eq_true ha)
          · simp [pathCovers,same] at hb
      simp [overlapWitness,admitted]
  | cons f rest ih =>
    cases b with
    | nil =>
      have admitted : bTail = .may ∨ f ∉ bE := by
        cases location with
        | nil => simp [pathCovers] at ha
        | cons g suffix =>
          by_cases same : f = g
          · subst g
            cases bTail with
            | may => exact Or.inl rfl
            | must => exact Or.inr (of_decide_eq_true hb)
          · simp [pathCovers,same] at ha
      simp [overlapWitness,admitted]
    | cons g suffix =>
      cases location with
      | nil => simp [pathCovers] at ha
      | cons x xs =>
        by_cases sameA : f = x
        · subst x
          by_cases sameB : g = f
          · subst g
            have restA : pathCovers aTail aE rest xs = true := by simpa [pathCovers] using ha
            have restB : pathCovers bTail bE suffix xs = true := by simpa [pathCovers] using hb
            have next := ih suffix xs restA restB
            simpa [overlapWitness] using next
          · simp [pathCovers,sameB] at hb
        · simp [pathCovers,sameA] at ha

theorem overlapWitness_iff (aTail bTail : Tail) (aE bE : List Nat) (a b : Path) :
    (overlapWitness aTail bTail aE bE a b).isSome = true ↔
      ∃ location, pathCovers aTail aE a location = true ∧
        pathCovers bTail bE b location = true := by
  constructor
  · intro h
    cases hw : overlapWitness aTail bTail aE bE a b with
    | none => simp [hw] at h
    | some w => exact ⟨w,overlapWitness_sound _ _ _ _ _ _ _ hw⟩
  · rintro ⟨w,ha,hb⟩
    exact overlapWitness_complete _ _ _ _ _ _ _ ha hb

theorem equal_anchor_overlap (aTail bTail : Tail) (aE bE : List Nat) (p : Path) :
    overlapWitness aTail bTail aE bE p p = some p := by
  induction p with
  | nil => rfl
  | cons f rest ih => simp [overlapWitness,ih]

theorem blocked_child_no_overlap (field : Nat) (childE : List Nat) (rest : Path) :
    overlapWitness .must .must [field] childE [] (field :: rest) = none := by
  simp [overlapWitness]

/-- FLOW is cofinite. These guards use E and mx as separate sets; atomization
is a semantic interpretation, never a finite-positive FLOW output channel. -/
def markAllowed (mx : List Nat) (mark : Nat) : Bool := decide (mark ∉ mx)

def mxSubset (small large : List Nat) : Prop := ∀ mark ∈ small, mark ∈ large

theorem mx_support (small large : List Nat) (mark : Nat)
    (sub : mxSubset small large) (allowed : markAllowed large mark = true) :
    markAllowed small mark = true := by
  apply decide_eq_true
  intro mem
  exact (of_decide_eq_true allowed) (sub mark mem)

/-- When child.mx ⊆ parent.mx, the whole parent allowed set is supplied by
its complete child. Retaining that child preserves its extra marks too. -/
theorem flow_fill_guard (parentMx childMx e : List Nat) (field mark : Nat)
    (location : Path) (support : mxSubset childMx parentMx) :
    ((markAllowed parentMx mark && pathCovers .must (fillExclusion e field) [] location) ||
      (markAllowed childMx mark && pathCovers .must [] [field] location)) =
    ((markAllowed parentMx mark && pathCovers .must e [] location) ||
      (markAllowed childMx mark && pathCovers .must [] [field] location)) := by
  cases hp : markAllowed parentMx mark with
  | false => simp
  | true =>
    have hc := mx_support childMx parentMx mark support hp
    simp only [hc, Bool.true_and]
    rw [direct_child_fill]
    simp

/-- A cover with fewer excluded marks supports every supplied child mark. -/
theorem flow_descendant_guard (parentMx childMx e childE : List Nat)
    (field mark : Nat) (rest location : Path)
    (marks : mxSubset parentMx childMx) (fieldAllowed : field ∉ e)
    (child : (markAllowed childMx mark && pathCovers .must childE (field :: rest) location) = true) :
    (markAllowed parentMx mark && pathCovers .must e [] location) = true := by
  have ⟨hm,hp⟩ := Bool.and_eq_true_iff.mp child
  exact Bool.and_eq_true_iff.mpr ⟨mx_support parentMx childMx mark marks hm,
    admitted_descendant .must e childE field rest location (Or.inr fieldAllowed) hp⟩

/-- A narrower FLOW child is insufficient: clearing the parent's hole would
supply mark 0 at field 1, though neither old row supplies that point. -/
theorem narrower_flow_child_cannot_fill :
    ((markAllowed [] 0 && pathCovers .must [1] [] [1]) ||
      (markAllowed [0] 0 && pathCovers .must [] [1] [1])) = false ∧
    (markAllowed [] 0 && pathCovers .must [] [] [1]) = true := by
  simp [markAllowed,pathCovers]

/-- The selected new reverse gate can call this witness only after checking
MUST-derived opposite-reader provenance and all original mark/mx guards. This
law certifies field overlap, not NORMAL authority or a new result layer. -/
def reverseOverlapEligible (mustDerived opposite : Bool) (aTail bTail : Tail)
    (aE bE : List Nat) (a b : Path) : Bool :=
  mustDerived && opposite && (overlapWitness aTail bTail aE bE a b).isSome

theorem ordinary_reader_unchanged (opposite : Bool) (aTail bTail : Tail)
    (aE bE : List Nat) (a b : Path) :
    reverseOverlapEligible false opposite aTail bTail aE bE a b = false := rfl

theorem same_direction_overlap_disabled (derived : Bool) (aTail bTail : Tail)
    (aE bE : List Nat) (a b : Path) :
    reverseOverlapEligible derived false aTail bTail aE bE a b = false := by
  simp [reverseOverlapEligible]

/-- This kernel proves executable spatial union preservation and exact finite
region overlap. It does not assert old C2 observational equivalence; the selected
C2 policy consumes canonical rows only. Runtime mark/source callbacks and the
MUST-derived inverse-output construction remain separate correspondence gates. -/
def proofScope : String := "finite atomized same-tail exact-header regions; cross-E union, direct-child refill, constructive overlap"

end FlowAntichains.Canonical
