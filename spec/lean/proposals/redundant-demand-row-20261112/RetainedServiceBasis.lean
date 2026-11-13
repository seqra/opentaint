import AncestorMayPointQuery

namespace RetainedServiceBasis
open AncestorMayPointQuery

inductive EntryKind where | data | zero | target
  deriving DecidableEq, Repr
inductive ExitKind where | data | zero
  deriving DecidableEq, Repr
inductive Channel where | c2 | c5
  deriving DecidableEq, Repr

-- These flags concern AP base constructors only. pointBase includes legal
-- ClassStatic point patterns. ordinaryMayBase excludes the static anchor.
structure Input where
  kind : EntryKind
  base : Nat
  pointBase : Bool
  ordinaryMayBase : Bool
  path : List Nat
  mark : Mark
  tail : Tail
  excluded : List Nat
  deriving DecidableEq, Repr

def pointView (e : Input) : Entry :=
  ⟨e.base,e.pointBase,e.path,e.mark,e.tail,e.excluded⟩
def point (e : Input) : Bool := e.kind == .data && isPoint (pointView e)

inductive EntryKey where
  | literal (e : Input)
  | point (base : Nat) (path : List Nat) (mark : Mark)
  deriving DecidableEq, Repr
def entryKey (e : Input) : EntryKey :=
  if point e then .point e.base e.path e.mark else .literal e

def precisionWitness : EntryKey → Option Input
  | .point _ _ _ => none
  | .literal e => if e.kind == .data && e.tail == .may && e.excluded.isEmpty then some e else none

structure Row where
  nativeKey : Nat
  owner : Nat -- full project/method/context/block/physical entry identity
  exitPort : Nat
  exitKind : ExitKind
  entry : Input
  outputKey : Nat -- injectively decoded complete canonical typed selector
  deriving DecidableEq, Repr

def c2Check (a b : Row) : Bool := a.owner == b.owner && entryKey a.entry == entryKey b.entry
def sameOutput (a b : Row) : Bool :=
  a.owner == b.owner && a.exitPort == b.exitPort && a.exitKind == b.exitKind && a.outputKey == b.outputKey
def pointMayCheck (counted : Nat → Bool) (a b : Row) : Bool :=
  point a.entry && a.entry.ordinaryMayBase && b.entry.ordinaryMayBase && b.entry.kind == .data &&
  a.entry.base == b.entry.base && a.entry.mark == b.entry.mark &&
  b.entry.tail == .may && b.entry.excluded.isEmpty &&
  (a.entry.path == b.entry.path || firstExtension counted b.entry.path a.entry.path)
def c5Check (counted : Nat → Bool) (a b : Row) : Bool :=
  sameOutput a b && (entryKey a.entry == entryKey b.entry || pointMayCheck counted a b)

def mayExactImage (counted : Nat → Bool) (limit : Nat) (e : Input) (i : Template) : Bool :=
  e.kind == .data && e.ordinaryMayBase && (match e.mark with | .full _ => true | _ => false) &&
  e.tail == .may && e.excluded.isEmpty && i.base == e.base && i.mark == e.mark &&
  i.tail == .exact && i.excluded.isEmpty && fits counted limit i.path && fits counted limit e.path &&
  (i.path == e.path || firstExtension counted e.path i.path)

def image (counted : Nat → Bool) (limit run : Nat)
    (other : Input → List Template → Bool) (e : Input) (members : List Template) : Bool :=
  if point e then members.any (storePoint counted limit run (pointView e))
  else if e.kind == .data && e.tail == .may then
    members.any (mayExactImage counted limit e) || other e members
  else other e members

-- Arbitrary shared native full emission, including actual-derived layers.
def c2 {Offer Answer : Type} (emit : EntryKey → Offer → List Answer)
    (owner : Nat) (offer : Offer) (r : Row) : List Answer :=
  if r.owner == owner then emit (entryKey r.entry) offer else []
def c5 {Raw Answer : Type} (counted : Nat → Bool) (limit run : Nat)
    (other : Input → List Template → Bool)
    (program : Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (request : Request) (members : List Template) (raw : Raw) (r : Row) : List Answer :=
  if r.owner == request.owner && r.exitPort == request.exitPort &&
      image counted limit run other r.entry members then
    program r.owner r.exitPort r.exitKind r.outputKey members raw else []

theorem c2_equal {Offer Answer : Type} (emit : EntryKey → Offer → List Answer)
    (a b : Row) (h : c2Check a b = true) (owner : Nat) (offer : Offer) :
    c2 emit owner offer a = c2 emit owner offer b := by
  simp only [c2Check,Bool.and_eq_true,beq_iff_eq] at h
  simp [c2,h.1,h.2]

theorem equal_entry_images (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (other : Input → List Template → Bool) (a b : Input)
    (h : entryKey a = entryKey b) (members : List Template) :
    image counted limit run other a members = image counted limit run other b members := by
  by_cases pa : point a = true <;> by_cases pb : point b = true
  · have keys := h
    simp only [entryKey,pa,pb,↓reduceIte,EntryKey.point.injEq] at keys
    rcases keys with ⟨base,path,mark⟩
    have pva : isPoint (pointView a) = true := by
      have h := pa
      simp only [point,Bool.and_eq_true] at h
      exact h.2
    have pvb : isPoint (pointView b) = true := by
      have h := pb
      simp only [point,Bool.and_eq_true] at h
      exact h.2
    simp only [image,pa,pb,↓reduceIte]
    apply congrArg (List.any (l := members))
    funext i
    rw [late_store_point_exact counted limit run late (pointView a) pva i,
        late_store_point_exact counted limit run late (pointView b) pvb i]
    simp only [exactPoint,pva,pvb]
    simp [pointView,base,path,mark]
  · simp [entryKey,pa,pb] at h
  · simp [entryKey,pa,pb] at h
  · have same : a = b := by simpa [entryKey,pa,pb] using h
    rw [same]

theorem same_path_or_first_may_image (counted : Nat → Bool) (limit : Nat)
    (a b : Row) (h : pointMayCheck counted a b = true) (i : Template)
    (hi : exactPoint counted limit (pointView a.entry) i = true) :
    mayExactImage counted limit b.entry i = true := by
  simp only [pointMayCheck,Bool.and_eq_true,beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨pa,_⟩,ordinary⟩,kind⟩,base⟩,mark⟩,tail⟩,empty⟩,extension⟩
  have pva : isPoint (pointView a.entry) = true := by
      have h := pa
      simp only [point,Bool.and_eq_true] at h
      exact h.2
  simp only [exactPoint,Bool.and_eq_true,beq_iff_eq] at hi
  rcases hi with ⟨⟨⟨⟨⟨⟨_,ib⟩,ip⟩,im⟩,it⟩,ie⟩,budget⟩
  have pref : b.entry.path <+: a.entry.path := by
    have alternatives := extension
    simp only [Bool.or_eq_true,beq_iff_eq] at alternatives
    rcases alternatives with same | first
    · rw [same]
      exact ⟨[],List.append_nil _⟩
    · exact extension_prefix counted _ _ first
  have allowed := extension
  have parentBudget := prefix_budget counted limit _ _ pref budget
  have full : (match b.entry.mark with | .full _ => true | _ => false) = true := by
    rw [←mark]
    cases hm : a.entry.mark <;> simp [isPoint,pointView,hm] at pva ⊢
  change fits counted limit a.entry.path = true at budget
  change i.base = a.entry.base at ib
  change i.path = a.entry.path at ip
  change i.mark = a.entry.mark at im
  have baseSelf : (b.entry.base == b.entry.base) = true := beq_iff_eq.mpr rfl
  have markSelf : (b.entry.mark == b.entry.mark) = true := beq_iff_eq.mpr rfl
  simp only [mayExactImage,kind,ordinary,full,tail,empty,ib,ip,im,it,ie,base,mark,budget,parentBudget,allowed,baseSelf,markSelf,Bool.and_self,Bool.true_and,Bool.and_true]
  rfl

theorem point_may_image_containment (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (other : Input → List Template → Bool) (a b : Row)
    (h : pointMayCheck counted a b = true) (members : List Template) :
    image counted limit run other a.entry members = true →
      image counted limit run other b.entry members = true := by
  have facts := h
  simp only [pointMayCheck,Bool.and_eq_true,beq_iff_eq] at facts
  have pa := facts.1.1.1.1.1.1.1.1
  have bk := facts.1.1.1.1.1.2
  have bt := facts.1.1.2
  have pb : point b.entry = false := by simp [point,pointView,isPoint,bt]
  have pva : isPoint (pointView a.entry) = true := by
      have h := pa
      simp only [point,Bool.and_eq_true] at h
      exact h.2
  simp only [image,pa,pb,bk,bt,beq_self_eq_true,Bool.true_and,Bool.false_eq_true,ite_false,↓reduceIte,Bool.or_eq_true]
  intro found
  obtain ⟨i,hi,good⟩ := List.any_eq_true.mp found
  rw [late_store_point_exact counted limit run late (pointView a.entry) pva i] at good
  exact Or.inl (List.any_eq_true.mpr ⟨i,hi,same_path_or_first_may_image counted limit a b h i good⟩)

theorem checked_image_containment (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (other : Input → List Template → Bool) (a b : Row)
    (h : c5Check counted a b = true) (members : List Template) :
    image counted limit run other a.entry members = true →
      image counted limit run other b.entry members = true := by
  simp only [c5Check,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at h
  rcases h.2 with equal | may
  · rw [equal_entry_images counted limit run late other a.entry b.entry equal members]
    exact id
  · exact point_may_image_containment counted limit run late other a b may members

theorem c5_contained {Raw Answer : Type}
    (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (other : Input → List Template → Bool)
    (program : Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (a b : Row) (h : c5Check counted a b = true)
    (request : Request) (members : List Template) (raw : Raw) (answer : Answer) :
    answer ∈ c5 counted limit run other program request members raw a →
      answer ∈ c5 counted limit run other program request members raw b := by
  have parts := h
  simp only [c5Check,Bool.and_eq_true] at parts
  have output := parts.1
  simp only [sameOutput,Bool.and_eq_true,beq_iff_eq] at output
  rcases output with ⟨⟨⟨ho,hp⟩,hk⟩,hout⟩
  unfold c5
  split
  · rename_i yes
    simp only [Bool.and_eq_true,beq_iff_eq] at yes
    have acceptedB := checked_image_containment counted limit run late other a b h members yes.2
    have yesB : (b.owner == request.owner && b.exitPort == request.exitPort &&
        image counted limit run other b.entry members) = true := by
      simp only [Bool.and_eq_true,beq_iff_eq]
      exact ⟨⟨ho.symm.trans yes.1.1,hp.symm.trans yes.1.2⟩,acceptedB⟩
    simp only [yesB,↓reduceIte]
    rw [←ho,←hp,←hk,←hout]
    exact id
  · simp

structure C2Profile where
  owner : Nat
  entry : EntryKey
  deriving DecidableEq, Repr
structure C5Profile where
  owner : Nat
  exitPort : Nat
  exitKind : ExitKind
  outputKey : Nat
  deriving DecidableEq, Repr
inductive Atom (Answer : Type) where
  | data (value : Answer)
  | entrySupport (value : C2Profile)
  | outputSupport (value : C5Profile)
  deriving DecidableEq

-- These are observation/profile atoms, not fabricated data publications.
-- A literal MAY signature preserves its complete ANY-cursor witness. Point
-- signatures contain the same entry path/mark/trie support and no cursor.
def c2Profile (r : Row) : C2Profile := ⟨r.owner,entryKey r.entry⟩
def c5Profile (r : Row) : C5Profile := ⟨r.owner,r.exitPort,r.exitKind,r.outputKey⟩
def metadata {Offer Raw Answer : Type} (r : Row) : NativeQuery Offer Raw → List (Atom Answer)
  | .c2 owner _ => if r.owner == owner then [.entrySupport (c2Profile r)] else []
  | .c5 request _ _ =>
      if r.owner == request.owner && r.exitPort == request.exitPort then [.outputSupport (c5Profile r)] else []

def dataReply {Offer Raw Answer : Type} (counted : Nat → Bool) (limit run : Nat)
    (emit : EntryKey → Offer → List Answer) (other : Input → List Template → Bool)
    (program : Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (r : Row) : NativeQuery Offer Raw → List Answer
  | .c2 owner offer => c2 emit owner offer r
  | .c5 request members raw => c5 counted limit run other program request members raw r
def reply {Offer Raw Answer : Type} (counted : Nat → Bool) (limit run : Nat)
    (emit : EntryKey → Offer → List Answer) (other : Input → List Template → Bool)
    (program : Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (r : Row) (q : NativeQuery Offer Raw) : List (Atom Answer) :=
  (dataReply counted limit run emit other program r q).map Atom.data ++ metadata r q

theorem c2_profiles_equal (a b : Row) (h : c2Check a b = true) : c2Profile a = c2Profile b := by
  simp only [c2Check,Bool.and_eq_true,beq_iff_eq] at h
  simp [c2Profile,h.1,h.2]
theorem c2_precision_profiles_equal (a b : Row) (h : c2Check a b = true) :
    precisionWitness (entryKey a.entry) = precisionWitness (entryKey b.entry) := by
  simp only [c2Check,Bool.and_eq_true,beq_iff_eq] at h
  rw [h.2]
theorem point_never_supplies_precision (e : Input) (h : point e = true) :
    precisionWitness (entryKey e) = none := by simp only [entryKey,h,↓reduceIte,precisionWitness]
theorem c5_profiles_equal (counted : Nat → Bool) (a b : Row) (h : c5Check counted a b = true) :
    c5Profile a = c5Profile b := by
  have hh := h
  simp only [c5Check,sameOutput,Bool.and_eq_true,beq_iff_eq] at hh
  rcases hh.1 with ⟨⟨⟨owner,port⟩,kind⟩,output⟩
  simp [c5Profile,owner,port,kind,output]

theorem c2_rich_reply_equal {Offer Raw Answer : Type}
    (counted : Nat → Bool) (limit run : Nat)
    (emit : EntryKey → Offer → List Answer) (other : Input → List Template → Bool)
    (program : Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (a b : Row) (h : c2Check a b = true) (owner : Nat) (offer : Offer) :
    reply counted limit run emit other program a (.c2 owner offer) =
      reply counted limit run emit other program b (.c2 owner offer) := by
  have same := c2_equal emit a b h owner offer
  have profiles := c2_profiles_equal a b h
  have ownerEq : a.owner = b.owner := by
    simp only [c2Check,Bool.and_eq_true,beq_iff_eq] at h
    exact h.1
  simp [reply,dataReply,same,metadata,profiles,ownerEq]

theorem c5_rich_reply_contained {Offer Raw Answer : Type}
    (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (emit : EntryKey → Offer → List Answer) (other : Input → List Template → Bool)
    (program : Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (a b : Row) (h : c5Check counted a b = true)
    (request : Request) (members : List Template) (raw : Raw) (answer : Atom Answer) :
    answer ∈ reply counted limit run emit other program a (.c5 request members raw) →
      answer ∈ reply counted limit run emit other program b (.c5 request members raw) := by
  have profiles := c5_profiles_equal counted a b h
  have output := h
  simp only [c5Check,sameOutput,Bool.and_eq_true,beq_iff_eq] at output
  have ho := output.1.1.1.1
  have hp := output.1.1.1.2
  simp only [reply,List.mem_append]
  intro found
  rcases found with data | support
  · obtain ⟨value,hv,same⟩ := List.mem_map.mp data
    apply Or.inl
    exact List.mem_map.mpr ⟨value,c5_contained counted limit run late other program a b h request members raw value hv,same⟩
  · apply Or.inr
    simpa only [metadata,ho,hp,profiles] using support

theorem split_row_cover {Offer Raw Answer : Type}
    (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (emit : EntryKey → Offer → List Answer) (other : Input → List Template → Bool)
    (program : Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (x z y : Row) (hz : c2Check x z = true) (hy : c5Check counted x y = true)
    (q : NativeQuery Offer Raw) (answer : Atom Answer) :
    answer ∈ reply counted limit run emit other program x q →
      answer ∈ reply counted limit run emit other program z q ∨
      answer ∈ reply counted limit run emit other program y q := by
  cases q with
  | c2 owner offer => rw [c2_rich_reply_equal counted limit run emit other program x z hz owner offer];exact Or.inl
  | c5 request members raw =>
    intro h
    exact Or.inr (c5_rich_reply_contained counted limit run late emit other program x y hy request members raw answer h)

-- Efficient finite binding uses tree-backed lookup functions, not list indexing.
structure Origin where
  retained : Bool
  completeEmissions : List Nat
  deriving DecidableEq, Repr
structure Witness where
  row : Nat
  origin : Nat
  deriving DecidableEq, Repr
structure Certificate where
  sourceRow : Nat
  c2 : Witness
  c5 : Witness
  deriving DecidableEq, Repr
structure Removal where
  origin : Nat
  certificates : List Certificate
  deriving DecidableEq, Repr

def validWitness (originAt : Nat → Option Origin) (w : Witness) : Bool :=
  match originAt w.origin with
  | none => false
  | some origin => origin.retained && origin.completeEmissions.contains w.row
def checkCertificate (counted : Nat → Bool) (rowAt : Nat → Option Row)
    (originAt : Nat → Option Origin) (c : Certificate) : Bool :=
  match rowAt c.sourceRow,rowAt c.c2.row,rowAt c.c5.row with
  | some x,some z,some y => validWitness originAt c.c2 && validWitness originAt c.c5 && c2Check x z && c5Check counted x y
  | _,_,_ => false
def checkRemoval (counted : Nat → Bool) (rowAt : Nat → Option Row)
    (originAt : Nat → Option Origin) (r : Removal) : Bool :=
  match originAt r.origin with
  | none => false
  | some source => !source.retained && !source.completeEmissions.isEmpty && source.completeEmissions.all (fun id =>
      r.certificates.any (fun c => c.sourceRow == id && checkCertificate counted rowAt originAt c))
def checkAll (counted : Nat → Bool) (rowAt : Nat → Option Row)
    (originAt : Nat → Option Origin) (removals : List Removal) : Bool :=
  removals.all (checkRemoval counted rowAt originAt)

theorem checked_witness (originAt : Nat → Option Origin) (w : Witness)
    (h : validWitness originAt w = true) :
    ∃ o, originAt w.origin = some o ∧ o.retained = true ∧ w.row ∈ o.completeEmissions := by
  unfold validWitness at h
  split at h
  · contradiction
  · rename_i o ho
    simp only [Bool.and_eq_true,List.contains_iff_mem] at h
    exact ⟨o,ho,h.1,h.2⟩

theorem checked_certificate (counted : Nat → Bool) (rowAt : Nat → Option Row)
    (originAt : Nat → Option Origin) (c : Certificate)
    (h : checkCertificate counted rowAt originAt c = true) :
    ∃ x z y, rowAt c.sourceRow = some x ∧ rowAt c.c2.row = some z ∧ rowAt c.c5.row = some y ∧
      validWitness originAt c.c2 = true ∧ validWitness originAt c.c5 = true ∧
      c2Check x z = true ∧ c5Check counted x y = true := by
  unfold checkCertificate at h
  split at h
  · rename_i x z y hx hz hy
    simp only [Bool.and_eq_true] at h
    exact ⟨x,z,y,hx,hz,hy,h.1.1.1,h.1.1.2,h.1.2,h.2⟩
  · contradiction

theorem checked_removal_complete (counted : Nat → Bool) (rowAt : Nat → Option Row)
    (originAt : Nat → Option Origin) (r : Removal)
    (h : checkRemoval counted rowAt originAt r = true) :
    ∃ o, originAt r.origin = some o ∧ o.retained = false ∧
      ∀ id ∈ o.completeEmissions, ∃ c ∈ r.certificates, c.sourceRow = id ∧ checkCertificate counted rowAt originAt c = true := by
  unfold checkRemoval at h
  split at h
  · contradiction
  · rename_i o ho
    simp only [Bool.and_eq_true,List.all_eq_true,List.any_eq_true,beq_iff_eq] at h
    have no : o.retained = false := by
      cases he : o.retained
      · rfl
      · simp [he] at h
    exact ⟨o,ho,no,h.2⟩

theorem zero_emission_removal_rejected (counted : Nat → Bool) (rowAt : Nat → Option Row)
    (originAt : Nat → Option Origin) (r : Removal) (o : Origin)
    (ho : originAt r.origin = some o) (empty : o.completeEmissions = []) :
    checkRemoval counted rowAt originAt r = false := by
  simp [checkRemoval,ho,empty]

theorem retired_witness_rejected (originAt : Nat → Option Origin) (w : Witness)
    (o : Origin) (ho : originAt w.origin = some o) (retired : o.retained = false) :
    validWitness originAt w = false := by simp [validWitness,ho,retired]

theorem checked_removal_retains_origin (counted : Nat → Bool) (rowAt : Nat → Option Row)
    (originAt : Nat → Option Origin) (r : Removal) (checked : checkRemoval counted rowAt originAt r = true) :
    ∃ id o, originAt id = some o ∧ o.retained = true := by
  obtain ⟨origin,ho,_,complete⟩ := checked_removal_complete counted rowAt originAt r checked
  have nonempty : origin.completeEmissions ≠ [] := by
    intro empty
    rw [zero_emission_removal_rejected counted rowAt originAt r origin ho empty] at checked
    contradiction
  cases he : origin.completeEmissions with
  | nil => exact False.elim (nonempty he)
  | cons first rest =>
    obtain ⟨c,_,_,good⟩ := complete first (by simp only [he,List.mem_cons,eq_self_iff_true,true_or])
    obtain ⟨_,_,_,_,_,_,keep,_,_,_⟩ := checked_certificate counted rowAt originAt c good
    obtain ⟨leaf,hLeaf,hKeep,_⟩ := checked_witness originAt c.c2 keep
    exact ⟨c.c2.origin,leaf,hLeaf,hKeep⟩

theorem c2_check_transitive (a b c : Row) (ab : c2Check a b = true) (bc : c2Check b c = true) :
    c2Check a c = true := by
  simp only [c2Check,Bool.and_eq_true,beq_iff_eq] at ab bc ⊢
  exact ⟨ab.1.trans bc.1,ab.2.trans bc.2⟩

theorem checked_c5_semantic_composition {Offer Raw Answer : Type}
    (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (emit : EntryKey → Offer → List Answer) (other : Input → List Template → Bool)
    (program : Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (a b c : Row) (ab : c5Check counted a b = true) (bc : c5Check counted b c = true)
    (request : Request) (members : List Template) (raw : Raw) (answer : Atom Answer) :
    answer ∈ reply counted limit run emit other program a (.c5 request members raw) →
      answer ∈ reply counted limit run emit other program c (.c5 request members raw) := by
  intro h
  exact c5_rich_reply_contained counted limit run late emit other program b c bc request members raw answer
    (c5_rich_reply_contained counted limit run late emit other program a b ab request members raw answer h)

def rowAnswers {Query Answer : Type} (respond : Row → Query → List Answer)
    (rowAt : Nat → Option Row) (id : Nat) (q : Query) : List Answer :=
  match rowAt id with | none => [] | some row => respond row q
def originAnswers {Query Answer : Type} (respond : Row → Query → List Answer)
    (rowAt : Nat → Option Row) (originAt : Nat → Option Origin) (id : Nat) (q : Query) : List Answer :=
  match originAt id with
  | none => []
  | some origin => origin.completeEmissions.flatMap (fun row => rowAnswers respond rowAt row q)
def retainedAnswer {Query Answer : Type} (respond : Row → Query → List Answer)
    (rowAt : Nat → Option Row) (originAt : Nat → Option Origin) (q : Query) (answer : Answer) : Prop :=
  ∃ id origin, originAt id = some origin ∧ origin.retained = true ∧
    answer ∈ originAnswers respond rowAt originAt id q

theorem origin_answer_member {Query Answer : Type} (respond : Row → Query → List Answer)
    (rowAt : Nat → Option Row) (originAt : Nat → Option Origin) (id : Nat) (q : Query) (answer : Answer)
    (h : answer ∈ originAnswers respond rowAt originAt id q) :
    ∃ origin rowId row, originAt id = some origin ∧ rowId ∈ origin.completeEmissions ∧
      rowAt rowId = some row ∧ answer ∈ respond row q := by
  cases ho : originAt id with
  | none => simp [originAnswers,ho] at h
  | some origin =>
    have found : answer ∈ origin.completeEmissions.flatMap (fun row => rowAnswers respond rowAt row q) := by
      simpa only [originAnswers,ho] using h
    obtain ⟨rowId,hr,ha⟩ := List.mem_flatMap.mp found
    cases hw : rowAt rowId with
    | none => simp [rowAnswers,hw] at ha
    | some row => exact ⟨origin,rowId,row,rfl,hr,hw,by simpa only [rowAnswers,hw] using ha⟩

theorem origin_answer_of_member {Query Answer : Type} (respond : Row → Query → List Answer)
    (rowAt : Nat → Option Row) (originAt : Nat → Option Origin)
    (id : Nat) (origin : Origin) (rowId : Nat) (row : Row) (q : Query) (answer : Answer)
    (ho : originAt id = some origin) (hr : rowId ∈ origin.completeEmissions)
    (hw : rowAt rowId = some row) (ha : answer ∈ respond row q) :
    answer ∈ originAnswers respond rowAt originAt id q := by
  simp only [originAnswers,ho]
  apply List.mem_flatMap.mpr
  exact ⟨rowId,hr,by simpa only [rowAnswers,hw] using ha⟩

theorem certificate_supplies_retained_answer {Offer Raw Answer : Type}
    (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (emit : EntryKey → Offer → List Answer) (other : Input → List Template → Bool)
    (program : Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (rowAt : Nat → Option Row) (originAt : Nat → Option Origin)
    (c : Certificate) (checked : checkCertificate counted rowAt originAt c = true)
    (source : Row) (hs : rowAt c.sourceRow = some source)
    (q : NativeQuery Offer Raw) (answer : Atom Answer)
    (found : answer ∈ reply counted limit run emit other program source q) :
    retainedAnswer (reply counted limit run emit other program) rowAt originAt q answer := by
  obtain ⟨x,z,y,hx,hz,hy,wz,wy,cz,cy⟩ := checked_certificate counted rowAt originAt c checked
  have same : x = source := Option.some.inj (hx.symm.trans hs)
  subst x
  have provided := split_row_cover counted limit run late emit other program source z y cz cy q answer found
  rcases provided with byZ | byY
  · obtain ⟨origin,ho,keep,member⟩ := checked_witness originAt c.c2 wz
    exact ⟨c.c2.origin,origin,ho,keep,
      origin_answer_of_member _ rowAt originAt _ origin _ z q answer ho member hz byZ⟩
  · obtain ⟨origin,ho,keep,member⟩ := checked_witness originAt c.c5 wy
    exact ⟨c.c5.origin,origin,ho,keep,
      origin_answer_of_member _ rowAt originAt _ origin _ y q answer ho member hy byY⟩

theorem complete_removal_supplies_retained_answer {Offer Raw Answer : Type}
    (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (emit : EntryKey → Offer → List Answer) (other : Input → List Template → Bool)
    (program : Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (rowAt : Nat → Option Row) (originAt : Nat → Option Origin)
    (r : Removal) (checked : checkRemoval counted rowAt originAt r = true)
    (q : NativeQuery Offer Raw) (answer : Atom Answer)
    (found : answer ∈ originAnswers (reply counted limit run emit other program) rowAt originAt r.origin q) :
    retainedAnswer (reply counted limit run emit other program) rowAt originAt q answer := by
  obtain ⟨origin,rowId,row,ho,member,hw,good⟩ := origin_answer_member _ rowAt originAt r.origin q answer found
  obtain ⟨source,hs,_,complete⟩ := checked_removal_complete counted rowAt originAt r checked
  have same : source = origin := Option.some.inj (hs.symm.trans ho)
  subst source
  obtain ⟨c,_,id,certified⟩ := complete rowId member
  have hrow : rowAt c.sourceRow = some row := by rw [id];exact hw
  exact certificate_supplies_retained_answer counted limit run late emit other program rowAt originAt c certified row hrow q answer good

-- All unprovided rows, marked/control stores and other state remain arbitrary
-- common parameters. Missing lookup entries are never a claim of global absence.
def beforeOracle {Query Answer : Type} (respond : Row → Query → List Answer)
    (rowAt : Nat → Option Row) (originAt : Nat → Option Origin)
    (common : Query → Answer → Prop) (removals : List Removal) (q : Query) (answer : Answer) : Prop :=
  common q answer ∨ retainedAnswer respond rowAt originAt q answer ∨
    answer ∈ removals.flatMap (fun r => originAnswers respond rowAt originAt r.origin q)
def afterOracle {Query Answer : Type} (respond : Row → Query → List Answer)
    (rowAt : Nat → Option Row) (originAt : Nat → Option Origin)
    (common : Query → Answer → Prop) (q : Query) (answer : Answer) : Prop :=
  common q answer ∨ retainedAnswer respond rowAt originAt q answer

theorem checked_complete_oracles_equal {Offer Raw Answer : Type}
    (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (emit : EntryKey → Offer → List Answer) (other : Input → List Template → Bool)
    (program : Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (rowAt : Nat → Option Row) (originAt : Nat → Option Origin)
    (common : NativeQuery Offer Raw → Atom Answer → Prop) (removals : List Removal)
    (checked : checkAll counted rowAt originAt removals = true) :
    beforeOracle (reply counted limit run emit other program) rowAt originAt common removals =
      afterOracle (reply counted limit run emit other program) rowAt originAt common := by
  funext q answer
  apply propext
  constructor
  · intro found
    rcases found with shared | retained | removed
    · exact Or.inl shared
    · exact Or.inr retained
    · obtain ⟨r,hr,has⟩ := List.mem_flatMap.mp removed
      have cert := List.all_eq_true.mp checked r hr
      exact Or.inr (complete_removal_supplies_retained_answer counted limit run late emit other program rowAt originAt r cert q answer has)
  · intro found
    rcases found with shared | retained
    · exact Or.inl shared
    · exact Or.inr (Or.inl retained)

theorem checked_all_future_iterations {Offer Raw Answer State : Type}
    (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (emit : EntryKey → Offer → List Answer) (other : Input → List Template → Bool)
    (program : Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (rowAt : Nat → Option Row) (originAt : Nat → Option Origin)
    (common : NativeQuery Offer Raw → Atom Answer → Prop) (removals : List Removal)
    (checked : checkAll counted rowAt originAt removals = true)
    (step : (NativeQuery Offer Raw → Atom Answer → Prop) → State → State) (n : Nat) (initial : State) :
    iterate step (beforeOracle (reply counted limit run emit other program) rowAt originAt common removals) n initial =
      iterate step (afterOracle (reply counted limit run emit other program) rowAt originAt common) n initial := by
  rw [checked_complete_oracles_equal counted limit run late emit other program rowAt originAt common removals checked]

theorem old_and_new_recertified {Offer Raw Answer State : Type}
    (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (emit : EntryKey → Offer → List Answer) (other : Input → List Template → Bool)
    (program : Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (rowAt : Nat → Option Row) (originAt : Nat → Option Origin)
    (common : NativeQuery Offer Raw → Atom Answer → Prop) (oldRemoved newRemoved : List Removal)
    (checked : checkAll counted rowAt originAt (oldRemoved ++ newRemoved) = true)
    (step : (NativeQuery Offer Raw → Atom Answer → Prop) → State → State) (n : Nat) (initial : State) :
    iterate step (beforeOracle (reply counted limit run emit other program) rowAt originAt common (oldRemoved++newRemoved)) n initial =
      iterate step (afterOracle (reply counted limit run emit other program) rowAt originAt common) n initial := by
  exact checked_all_future_iterations counted limit run late emit other program rowAt originAt common _ checked step n initial

#print axioms c2_equal
#print axioms equal_entry_images
#print axioms same_path_or_first_may_image
#print axioms point_may_image_containment
#print axioms checked_image_containment
#print axioms c5_contained
#print axioms c2_profiles_equal
#print axioms c2_precision_profiles_equal
#print axioms point_never_supplies_precision
#print axioms c5_profiles_equal
#print axioms c2_rich_reply_equal
#print axioms c5_rich_reply_contained
#print axioms split_row_cover
#print axioms checked_witness
#print axioms checked_certificate
#print axioms checked_removal_complete
#print axioms zero_emission_removal_rejected
#print axioms retired_witness_rejected
#print axioms checked_removal_retains_origin
#print axioms c2_check_transitive
#print axioms checked_c5_semantic_composition
#print axioms origin_answer_member
#print axioms origin_answer_of_member
#print axioms certificate_supplies_retained_answer
#print axioms complete_removal_supplies_retained_answer
#print axioms checked_complete_oracles_equal
#print axioms checked_all_future_iterations
#print axioms old_and_new_recertified
end RetainedServiceBasis
