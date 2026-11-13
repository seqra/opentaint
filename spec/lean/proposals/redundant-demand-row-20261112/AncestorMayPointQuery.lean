import Std

namespace AncestorMayPointQuery

inductive Tail where | exact | star | may | must
  deriving DecidableEq, Repr
inductive Mark where | flow | full (id : Nat) | other (id : Nat)
  deriving DecidableEq, Repr

structure Entry where
  base : Nat
  ordinaryBase : Bool
  path : List Nat
  mark : Mark
  tail : Tail
  excluded : List Nat
  deriving DecidableEq, Repr

structure Row where
  owner : Nat -- complete project/method/context/block/physical-entry identity
  exitPort : Nat
  entry : Entry
  outputKey : Nat -- complete canonical output selector, decoded independently
  deriving DecidableEq, Repr

def isPoint (e : Entry) : Bool :=
  e.ordinaryBase && (match e.mark with | .full _ => true | _ => false) &&
    (e.tail == .star || (e.tail == .exact && e.excluded.isEmpty))

def firstCountedLength (counted : Nat → Bool) : List Nat → Option Nat
  | [] => none
  | a :: rest => if counted a then some 1 else (firstCountedLength counted rest).map Nat.succ

def firstExtension (counted : Nat → Bool) (parent child : List Nat) : Bool :=
  parent.isPrefixOf child && decide (parent.length < child.length) &&
    (firstCountedLength counted (child.drop parent.length) == some (child.length-parent.length))

def c2Witness (x z : Row) : Bool :=
  isPoint x.entry && isPoint z.entry && x.owner == z.owner &&
    x.entry.base == z.entry.base && x.entry.path == z.entry.path && x.entry.mark == z.entry.mark

def c5Witness (counted : Nat → Bool) (x y : Row) : Bool :=
  isPoint x.entry && x.owner == y.owner && x.exitPort == y.exitPort && x.outputKey == y.outputKey &&
    x.entry.base == y.entry.base && x.entry.mark == y.entry.mark &&
    y.entry.ordinaryBase && y.entry.tail == .may && y.entry.excluded.isEmpty &&
    firstExtension counted y.entry.path x.entry.path

def cover (counted : Nat → Bool) (x z y : Row) : Bool := c2Witness x z && c5Witness counted x y

structure Certificate where
  source : Nat
  c2 : Nat
  c5 : Nat
  deriving DecidableEq, Repr

def checkCertificate (counted : Nat → Bool) (rows : List Row) (retained : Nat → Bool) (c : Certificate) : Bool :=
  match rows[c.source]?, rows[c.c2]?, rows[c.c5]? with
  | some x, some z, some y => retained c.c2 && retained c.c5 && cover counted x z y
  | _, _, _ => false

theorem checked_certificate (counted : Nat → Bool) (rows : List Row) (retained : Nat → Bool)
    (c : Certificate) (checked : checkCertificate counted rows retained c = true) :
    ∃ x z y, rows[c.source]? = some x ∧ rows[c.c2]? = some z ∧ rows[c.c5]? = some y ∧
      retained c.c2 = true ∧ retained c.c5 = true ∧ cover counted x z y = true := by
  unfold checkCertificate at checked
  split at checked
  · rename_i x z y hx hz hy
    simp only [Bool.and_eq_true] at checked
    exact ⟨x,z,y,hx,hz,hy,checked.1.1,checked.1.2,checked.2⟩
  · contradiction

end AncestorMayPointQuery

namespace AncestorMayPointQuery

structure Template where
  base : Nat
  path : List Nat
  mark : Mark
  tail : Tail
  excluded : List Nat
  deriving DecidableEq, Repr

def fits (counted : Nat → Bool) (limit : Nat) (path : List Nat) : Bool :=
  decide ((path.filter counted).length ≤ limit)

def exactPoint (counted : Nat → Bool) (limit : Nat) (e : Entry) (i : Template) : Bool :=
  isPoint e && i.base == e.base && i.path == e.path && i.mark == e.mark &&
    i.tail == .exact && i.excluded.isEmpty && fits counted limit e.path

-- Native point C5 image, including both normalization and concrete-to-FLOW
-- companion fallbacks. The run-2 branch is explicit and disappears only by
-- the proved late-run premise. No protection/layer is part of a premise key.
def emitPoint (counted : Nat → Bool) (limit run : Nat) (e : Entry) (i : Template) : Bool :=
  isPoint e && i.base == e.base && i.path == e.path && i.mark == e.mark && fits counted limit e.path &&
    ((i.tail == .exact && i.excluded.isEmpty) ||
      (run == 2 && e.tail == .star && i.tail == .star && i.excluded == e.excluded))

def primaryPoint (counted : Nat → Bool) (limit run : Nat) (e : Entry) (i : Template) : Bool :=
  emitPoint counted limit run e i ||
    (i.mark == .flow && i.tail == .star && i.excluded.isEmpty &&
      emitPoint counted limit run e {i with tail := .exact})

def storePoint (counted : Nat → Bool) (limit run : Nat) (e : Entry) (i : Template) : Bool :=
  primaryPoint counted limit run e i ||
    (i.mark == .flow && i.tail == .star && i.excluded.isEmpty &&
      primaryPoint counted limit run e {i with mark := e.mark})

theorem late_store_point_exact (counted : Nat → Bool) (limit run : Nat)
    (late : 3 ≤ run) (e : Entry) (point : isPoint e = true) (i : Template) :
    storePoint counted limit run e i = exactPoint counted limit e i := by
  have ne : run ≠ 2 := by omega
  cases hm : e.mark with
  | flow => simp [isPoint,hm] at point
  | other n => simp [isPoint,hm] at point
  | full n =>
    cases hi : i.mark <;> cases ht : i.tail <;>
      apply Bool.eq_iff_iff.mpr <;>
      simp [storePoint,primaryPoint,emitPoint,exactPoint,ne,hm,hi,ht,point,
        Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,and_assoc,and_left_comm,and_comm]

theorem no_late_point_flow_companion (counted : Nat → Bool) (limit run : Nat)
    (late : 3 ≤ run) (e : Entry) (point : isPoint e = true) (i : Template)
    (flow : i.mark = .flow) : storePoint counted limit run e i = false := by
  rw [late_store_point_exact counted limit run late e point i]
  cases hm : e.mark <;> simp [isPoint,hm] at point
  simp [exactPoint,flow,hm]

def ancestorMayImage (counted : Nat → Bool) (limit : Nat) (e : Entry) (i : Template) : Bool :=
  e.ordinaryBase && (match e.mark with | .full _ => true | _ => false) &&
    e.tail == .may && e.excluded.isEmpty && i.base == e.base && i.mark == e.mark &&
    i.tail == .exact && i.excluded.isEmpty && fits counted limit i.path &&
    fits counted limit e.path && firstExtension counted e.path i.path

theorem extension_prefix (counted : Nat → Bool) (p q : List Nat)
    (h : firstExtension counted p q = true) : p <+: q := by
  simp only [firstExtension,Bool.and_eq_true] at h
  exact List.isPrefixOf_iff_prefix.mp h.1.1

theorem prefix_budget (counted : Nat → Bool) (limit : Nat) (p q : List Nat)
    (hpref : p <+: q) (hq : fits counted limit q = true) : fits counted limit p = true := by
  have length := (hpref.filter counted).length_le
  simp only [fits,decide_eq_true_eq] at hq ⊢
  omega

theorem checked_c5_contains_point (counted : Nat → Bool) (limit : Nat) (x y : Row)
    (cover : c5Witness counted x y = true) (i : Template)
    (point : exactPoint counted limit x.entry i = true) :
    ancestorMayImage counted limit y.entry i = true := by
  simp only [c5Witness,Bool.and_eq_true,beq_iff_eq] at cover
  rcases cover with ⟨⟨⟨⟨⟨⟨⟨⟨⟨xp,owner⟩,port⟩,output⟩,base⟩,mark⟩,ordinary⟩,tail⟩,empty⟩,extension⟩
  simp only [exactPoint,Bool.and_eq_true,beq_iff_eq] at point
  rcases point with ⟨⟨⟨⟨⟨⟨_,ib⟩,ip⟩,im⟩,it⟩,ie⟩,budget⟩
  have parentBudget := prefix_budget counted limit y.entry.path x.entry.path
    (extension_prefix counted _ _ extension) budget
  have full : (match y.entry.mark with | .full _ => true | _ => false) = true := by
    rw [← mark]
    cases hm : x.entry.mark <;> simp [isPoint,hm] at xp ⊢
  have bi : fits counted limit i.path = true := by rw [ip]; exact budget
  have ei : firstExtension counted y.entry.path i.path = true := by rw [ip]; exact extension
  simp only [ancestorMayImage,Bool.and_eq_true,beq_iff_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ordinary,full⟩,tail⟩,empty⟩,ib.trans base⟩,im.trans mark⟩,it⟩,ie⟩,bi⟩,parentBudget⟩,ei⟩

theorem late_point_whole_original_contained (counted : Nat → Bool) (limit run : Nat)
    (late : 3 ≤ run) (x y : Row) (cover : c5Witness counted x y = true) (members : List Template) :
    members.any (storePoint counted limit run x.entry) = true →
      members.any (ancestorMayImage counted limit y.entry) = true := by
  intro h
  obtain ⟨i,hi,good⟩ := List.any_eq_true.mp h
  have xp : isPoint x.entry = true := by
    simp only [c5Witness,Bool.and_eq_true] at cover
    exact cover.1.1.1.1.1.1.1.1.1
  rw [late_store_point_exact counted limit run late x.entry xp i] at good
  exact List.any_eq_true.mpr ⟨i,hi,checked_c5_contains_point counted limit x y cover i good⟩

end AncestorMayPointQuery

namespace AncestorMayPointQuery

-- The accepted concrete-point theorem identifies the complete native C2
-- family by this profile in every run>=3: EXACT output at the same path,
-- actual-derived NORMAL/DEMAND support, no FLOW companion and no cursor.
-- Its scalar/packet emitter is arbitrary here; equality uses equal full
-- profiles, not agreement on the finitely observed offers.
def profile (e : Entry) := (e.base,e.path,e.mark)
def pointC2 {Offer Answer : Type} (emit : (Nat × List Nat × Mark) → Offer → List Answer)
    (e : Entry) (offer : Offer) : List Answer :=
  if isPoint e then emit (profile e) offer else []

theorem checked_c2_equal {Offer Answer : Type}
    (emit : (Nat × List Nat × Mark) → Offer → List Answer) (x z : Row)
    (cover : c2Witness x z = true) (offer : Offer) :
    pointC2 emit x.entry offer = pointC2 emit z.entry offer := by
  simp only [c2Witness,Bool.and_eq_true,beq_iff_eq] at cover
  rcases cover with ⟨⟨⟨⟨⟨xp,zp⟩,_⟩,base⟩,path⟩,mark⟩
  simp [pointC2,profile,xp,zp,base,path,mark]

def suppliesPrecision (e : Entry) : Bool := e.tail == .may
theorem point_has_no_precision (e : Entry) (point : isPoint e = true) :
    suppliesPrecision e = false := by
  cases ht : e.tail <;> simp [isPoint,ht] at point ⊢
  all_goals simp [suppliesPrecision,ht]

-- Other native MAY images remain present through the already-retained Y.
-- This Boolean is additional entry behavior, not a future-safety premise.
def rowImage (counted : Nat → Bool) (limit run : Nat)
    (other : Row → List Template → Bool) (r : Row) (members : List Template) : Bool :=
  if isPoint r.entry then members.any (storePoint counted limit run r.entry)
  else if r.entry.tail == .may then
    members.any (ancestorMayImage counted limit r.entry) || other r members
  else other r members

theorem checked_row_image_contains (counted : Nat → Bool) (limit run : Nat)
    (late : 3 ≤ run) (other : Row → List Template → Bool) (x y : Row)
    (cover : c5Witness counted x y = true) (members : List Template) :
    rowImage counted limit run other x members = true →
      rowImage counted limit run other y members = true := by
  have pieces := cover
  simp only [c5Witness,Bool.and_eq_true,beq_iff_eq] at pieces
  have xp := pieces.1.1.1.1.1.1.1.1.1
  have yt : y.entry.tail = .may := pieces.1.1.2
  have yn : isPoint y.entry = false := by simp [isPoint,yt]
  intro h
  have source : members.any (storePoint counted limit run x.entry) = true := by
    simpa only [rowImage,xp,Bool.true_eq,↓reduceIte] using h
  have target := late_point_whole_original_contained counted limit run late x y cover members source
  simp only [rowImage,yn,yt,Bool.false_eq_true,↓reduceIte,beq_self_eq_true,Bool.or_eq_true]
  exact Or.inl target

structure Request where
  owner : Nat
  exitPort : Nat
  deriving DecidableEq, Repr

def rowC5 {Raw Answer : Type} (counted : Nat → Bool) (limit run : Nat)
    (other : Row → List Template → Bool)
    (program : Nat → Nat → Nat → List Template → Raw → List Answer)
    (request : Request) (members : List Template) (raw : Raw) (r : Row) : List Answer :=
  if r.owner == request.owner && r.exitPort == request.exitPort &&
      rowImage counted limit run other r members then
    program r.owner r.exitPort r.outputKey members raw
  else []

theorem checked_c5_reply_contained {Raw Answer : Type}
    (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (other : Row → List Template → Bool)
    (program : Nat → Nat → Nat → List Template → Raw → List Answer)
    (x y : Row) (cover : c5Witness counted x y = true)
    (request : Request) (members : List Template) (raw : Raw) (answer : Answer) :
    answer ∈ rowC5 counted limit run other program request members raw x →
      answer ∈ rowC5 counted limit run other program request members raw y := by
  have pieces := cover
  simp only [c5Witness,Bool.and_eq_true,beq_iff_eq] at pieces
  have owner : x.owner = y.owner := pieces.1.1.1.1.1.1.1.1.2
  have port : x.exitPort = y.exitPort := pieces.1.1.1.1.1.1.1.2
  have output : x.outputKey = y.outputKey := pieces.1.1.1.1.1.1.2
  unfold rowC5
  split
  · rename_i hx
    have hp := hx
    simp only [Bool.and_eq_true,beq_iff_eq] at hp
    have accepted := checked_row_image_contains counted limit run late other x y cover members hp.2
    have hy : (y.owner == request.owner && y.exitPort == request.exitPort &&
        rowImage counted limit run other y members) = true := by
      simp only [Bool.and_eq_true,beq_iff_eq]
      exact ⟨⟨owner.symm.trans hp.1.1,port.symm.trans hp.1.2⟩,accepted⟩
    rw [if_pos hy]
    simp only [←owner,←port,←output]
    exact id
  · simp

-- General complete-union replacement. Different retained rows may witness
-- C2 and C5; no unpaired synthetic query is constructed.
theorem retained_reply_union {R Answer : Type} (retained removed : List R)
    (reply : R → List Answer)
    (covers : ∀ x ∈ removed, ∀ answer ∈ reply x, ∃ y ∈ retained, answer ∈ reply y)
    (answer : Answer) :
    answer ∈ (retained++removed).flatMap reply ↔ answer ∈ retained.flatMap reply := by
  simp only [List.flatMap_append,List.mem_append]
  constructor
  · intro h
    cases h with
    | inl kept => exact kept
    | inr lost =>
      obtain ⟨x,hx,found⟩ := List.mem_flatMap.mp lost
      obtain ⟨y,hy,provided⟩ := covers x hx answer found
      exact List.mem_flatMap.mpr ⟨y,hy,provided⟩
  · exact Or.inl

def oracle {Query Answer : Type} [DecidableEq Answer]
    (reply : Row → Query → List Answer) (rows : List Row) : Query → Answer → Bool :=
  fun q a => decide (a ∈ rows.flatMap (fun r => reply r q))

theorem complete_query_oracle_equal {Query Answer : Type} [DecidableEq Answer]
    (reply : Row → Query → List Answer) (retained removed : List Row)
    (covers : ∀ q, ∀ x ∈ removed, ∀ answer ∈ reply x q,
      ∃ y ∈ retained, answer ∈ reply y q) :
    oracle reply (retained++removed) = oracle reply retained := by
  funext q a
  apply Bool.eq_iff_iff.mpr
  simpa only [oracle,decide_eq_true_eq] using
    retained_reply_union retained removed (fun r => reply r q) (covers q) a

def iterate {Oracle State : Type} (step : Oracle → State → State) (o : Oracle) : Nat → State → State
  | 0,s => s
  | n+1,s => iterate step o n (step o s)

theorem all_future_iterations {Query Answer State : Type} [DecidableEq Answer]
    (reply : Row → Query → List Answer) (retained removed : List Row)
    (covers : ∀ q, ∀ x ∈ removed, ∀ answer ∈ reply x q,
      ∃ y ∈ retained, answer ∈ reply y q)
    (step : (Query → Answer → Bool) → State → State) (n : Nat) (initial : State) :
    iterate step (oracle reply (retained++removed)) n initial =
      iterate step (oracle reply retained) n initial := by
  rw [complete_query_oracle_equal reply retained removed covers]

inductive NativeQuery (Offer Raw : Type) where
  | c2 (owner : Nat) (offer : Offer)
  | c5 (request : Request) (members : List Template) (raw : Raw)

def dispatch {Offer Raw Answer : Type}
    (counted : Nat → Bool) (limit run : Nat)
    (emit : (Nat × List Nat × Mark) → Offer → List Answer)
    (otherC2 : Row → Offer → List Answer) (otherImage : Row → List Template → Bool)
    (program : Nat → Nat → Nat → List Template → Raw → List Answer)
    (r : Row) : NativeQuery Offer Raw → List Answer
  | .c2 owner offer => if r.owner == owner then
      (if isPoint r.entry then pointC2 emit r.entry offer else otherC2 r offer) else []
  | .c5 request members raw => rowC5 counted limit run otherImage program request members raw r

theorem cover_dispatch {Offer Raw Answer : Type}
    (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (emit : (Nat × List Nat × Mark) → Offer → List Answer)
    (otherC2 : Row → Offer → List Answer) (otherImage : Row → List Template → Bool)
    (program : Nat → Nat → Nat → List Template → Raw → List Answer)
    (x z y : Row) (guard : cover counted x z y = true) (q : NativeQuery Offer Raw) (answer : Answer) :
    answer ∈ dispatch counted limit run emit otherC2 otherImage program x q →
      answer ∈ dispatch counted limit run emit otherC2 otherImage program z q ∨
      answer ∈ dispatch counted limit run emit otherC2 otherImage program y q := by
  have pair := guard
  simp only [cover,Bool.and_eq_true] at pair
  cases q with
  | c2 owner offer =>
    have cp := pair.1
    simp only [c2Witness,Bool.and_eq_true,beq_iff_eq] at cp
    have xp := cp.1.1.1.1.1
    have zp := cp.1.1.1.1.2
    have sameOwner := cp.1.1.1.2
    have same := checked_c2_equal emit x z pair.1 offer
    simp only [dispatch,xp,zp,↓reduceIte]
    rw [sameOwner,same]
    exact Or.inl
  | c5 request members raw =>
    intro found
    exact Or.inr (checked_c5_reply_contained counted limit run late otherImage program x y pair.2 request members raw answer found)

theorem structural_query_union_equal {Offer Raw Answer : Type} [DecidableEq Answer]
    (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (emit : (Nat × List Nat × Mark) → Offer → List Answer)
    (otherC2 : Row → Offer → List Answer) (otherImage : Row → List Template → Bool)
    (program : Nat → Nat → Nat → List Template → Raw → List Answer)
    (retained removed : List Row)
    (witnesses : ∀ x ∈ removed, ∃ z ∈ retained, ∃ y ∈ retained, cover counted x z y = true) :
    oracle (dispatch counted limit run emit otherC2 otherImage program) (retained++removed) =
      oracle (dispatch counted limit run emit otherC2 otherImage program) retained := by
  apply complete_query_oracle_equal
  intro q x hx answer found
  obtain ⟨z,hz,y,hy,good⟩ := witnesses x hx
  have supplied := cover_dispatch counted limit run late emit otherC2 otherImage program x z y good q answer found
  cases supplied with
  | inl byZ => exact ⟨z,hz,byZ⟩
  | inr byY => exact ⟨y,hy,byY⟩

theorem structural_all_future_iterations {Offer Raw Answer State : Type} [DecidableEq Answer]
    (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (emit : (Nat × List Nat × Mark) → Offer → List Answer)
    (otherC2 : Row → Offer → List Answer) (otherImage : Row → List Template → Bool)
    (program : Nat → Nat → Nat → List Template → Raw → List Answer)
    (retained removed : List Row)
    (witnesses : ∀ x ∈ removed, ∃ z ∈ retained, ∃ y ∈ retained, cover counted x z y = true)
    (step : (NativeQuery Offer Raw → Answer → Bool) → State → State) (n : Nat) (initial : State) :
    iterate step (oracle (dispatch counted limit run emit otherC2 otherImage program) (retained++removed)) n initial =
      iterate step (oracle (dispatch counted limit run emit otherC2 otherImage program) retained) n initial := by
  rw [structural_query_union_equal counted limit run late emit otherC2 otherImage program retained removed witnesses]

#print axioms checked_certificate
#print axioms late_store_point_exact
#print axioms no_late_point_flow_companion
#print axioms extension_prefix
#print axioms prefix_budget
#print axioms checked_c5_contains_point
#print axioms late_point_whole_original_contained
#print axioms checked_c2_equal
#print axioms point_has_no_precision
#print axioms checked_row_image_contains
#print axioms checked_c5_reply_contained
#print axioms retained_reply_union
#print axioms complete_query_oracle_equal
#print axioms all_future_iterations
#print axioms cover_dispatch
#print axioms structural_query_union_equal
#print axioms structural_all_future_iterations
end AncestorMayPointQuery
