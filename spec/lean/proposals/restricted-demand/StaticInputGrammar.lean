/- Selected consistency repair for all-run concrete STAR preservation.
   The old/candidate names below retain the historical domain comparison.
   Geometry closure only. The AP laws reuse selected correlated raw transfer.
   Caller supply, identity projection and accessor tags are explicit assumptions. -/
import ApSpec.Run1CorrelatedConcreteInitials

namespace RestrictedDemand.StaticInputGrammar
open ApSpec ApSpec.Run1CorrelatedConcreteInitials
set_option autoImplicit false

inductive Slot where
  | field (owner field : Nat)
  | marker (owner : Nat)
  | root
  | classWide (owner : Nat)
  deriving DecidableEq, Repr
inductive TailTag where
  | exact | any | star | must
  deriving DecidableEq, Repr
inductive ActualMark where
  | full (id : Nat)
  | group (id : Nat)
  | zero
  deriving DecidableEq, Repr
structure Input where
  slot : Slot
  suffix : List Acc
  tail : TailTag
  exclusion : Excl
  mark : ActualMark
  deriving DecidableEq, Repr

def fullMark : ActualMark → Prop
  | .full _ => True
  | _ => False

def oldGeometry (q : Input) : Prop :=
  match q.slot with
  | .field _ _ => q.suffix = [] ∧ q.exclusion = Excl.empty ∧
      (q.tail = .exact ∨ q.tail = .any)
  | .marker _ => q.suffix = [] ∧ q.tail = .exact ∧ q.exclusion = Excl.empty
  | _ => False

def candidateGeometry (q : Input) : Prop :=
  match q.slot with
  | .field _ _ => q.suffix = [] ∧ (q.tail = .exact ∨ q.tail = .any ∨ q.tail = .star) ∧
      (q.tail = .star ∨ q.exclusion = Excl.empty)
  | .marker _ => q.suffix = [] ∧ q.tail = .exact ∧ q.exclusion = Excl.empty
  | _ => False

def oldValid (q : Input) : Prop := fullMark q.mark ∧ oldGeometry q
def candidateValid (q : Input) : Prop := fullMark q.mark ∧ candidateGeometry q

def fieldStar (owner field mark : Nat) (e : Excl) : Input :=
  ⟨.field owner field, [], .star, e, .full mark⟩

theorem field_star_is_candidate (owner field mark : Nat) (e : Excl) :
    candidateValid (fieldStar owner field mark e) := by
  simp [candidateValid,fullMark,candidateGeometry,fieldStar]

theorem field_star_is_rejected_by_old_domain (owner field mark : Nat) (e : Excl) :
    ¬ oldValid (fieldStar owner field mark e) := by
  simp [oldValid,fullMark,oldGeometry,fieldStar]

/-- The candidate keeps all previously accepted FULL shapes. -/
theorem old_domain_in_candidate {q : Input} (h : oldValid q) : candidateValid q := by
  obtain ⟨hm,hg⟩ := h
  refine ⟨hm,?_⟩
  cases hs : q.slot with
  | field owner field =>
      simp only [oldGeometry,hs] at hg
      obtain ⟨hp,he,ht⟩ := hg
      simp only [candidateGeometry,hs]
      exact ⟨hp,ht.elim Or.inl (fun ha => Or.inr (Or.inl ha)),Or.inr he⟩
  | marker owner => simpa [oldGeometry,candidateGeometry,hs] using hg
  | root => simp [oldGeometry,hs] at hg
  | classWide owner => simp [oldGeometry,hs] at hg

theorem candidate_rejects_root (suffix : List Acc) (tail : TailTag) (e : Excl) (mark : ActualMark) :
    ¬ candidateValid ⟨.root,suffix,tail,e,mark⟩ := by
  simp [candidateValid,candidateGeometry]

theorem candidate_rejects_class_wide (owner : Nat) (suffix : List Acc)
    (tail : TailTag) (e : Excl) (mark : ActualMark) :
    ¬ candidateValid ⟨.classWide owner,suffix,tail,e,mark⟩ := by
  simp [candidateValid,candidateGeometry]

theorem candidate_rejects_must (slot : Slot) (suffix : List Acc) (e : Excl) (mark : ActualMark) :
    ¬ candidateValid ⟨slot,suffix,.must,e,mark⟩ := by
  cases slot <;> simp [candidateValid,candidateGeometry]

theorem candidate_rejects_group_actual (slot : Slot) (suffix : List Acc)
    (tail : TailTag) (e : Excl) (group : Nat) :
    ¬ candidateValid ⟨slot,suffix,tail,e,.group group⟩ := by
  simp [candidateValid,fullMark]

/-- Existing static binding projects the fact as is. This is an adapter assumption. -/
def projectStatic (q : Input) : Input := q

theorem same_slot_projection_preserves_all_headers (q : Input) : projectStatic q = q := rfl

theorem same_slot_projection_closed {q : Input} (h : candidateValid q) :
    candidateValid (projectStatic q) := h

/-- A class tag costs zero and the named field costs one. A further counted
    suffix loses correlation under the EXISTING bound, not under validation. -/
def bound1 (q : Input) : Input :=
  match q.slot, q.suffix with
  | .field _ _, _ :: _ => { q with suffix := [], tail := .any, exclusion := Excl.empty }
  | _, _ => q

def relay1 (q : Input) : Input := bound1 (projectStatic q)

theorem bounded_field_star_relay (owner field mark : Nat) (e : Excl) :
    relay1 (fieldStar owner field mark e) = fieldStar owner field mark e := rfl

theorem bounded_field_star_relay_closed (owner field mark : Nat) (e : Excl) :
    candidateValid (relay1 (fieldStar owner field mark e)) := field_star_is_candidate _ _ _ _

/-- Assume a non-MUST backward input with a legal E. The existing field limit
    removes a deeper counted suffix before this input validator runs. -/
theorem overflow_field_relay_is_bounded (owner field mark first : Nat)
    (rest : List Acc) (tail : TailTag) (e : Excl)
    (_notMust : tail ≠ .must) (_legalE : tail = .star ∨ e = Excl.empty) :
    candidateValid (relay1 ⟨.field owner field,first :: rest,tail,e,.full mark⟩) := by
  simp [candidateValid,fullMark,candidateGeometry,relay1,projectStatic,bound1]

theorem repeated_bounded_star_relay (steps owner field mark : Nat) (e : Excl) :
    (List.replicate steps ()).foldl (fun q _ => relay1 q) (fieldStar owner field mark e) =
      fieldStar owner field mark e := by
  induction steps with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ,relay1,projectStatic,bound1,fieldStar] using ih

/-- The selected correlated AP, without the historical W2 STAR erasure. -/
def concreteStar (base : Base) (path : List Acc) (e : Excl) (mark : Mark) : PFact :=
  ⟨base,path,.star e,.conc mark⟩
def flowIdentity (base : Base) (path : List Acc) : PFact :=
  ⟨base,path,.star Excl.empty,.star⟩

theorem actual_AP_identity_keeps_concrete_star (base : Base) (path : List Acc)
    (e : Excl) (mark : Mark) (demand : Bool) :
    rawApply ⟨concreteStar base path e mark,demand⟩ (flowIdentity base path) (flowIdentity base path) =
      ⟨[⟨concreteStar base path e mark,demand⟩],[]⟩ := by
  cases e <;>
    simp [rawApply,concreteStar,flowIdentity,relate,
      CoreAux.dropPrefix_some.mpr (List.append_nil path).symm,belowCase,admitsTailB,
      tailExcl,Excl.union,Excl.empty,Excl.admits,markGate,markComp]

/-- Adapter assumptions: the class accessor is uncounted and the field is counted. -/
theorem actual_AP_limit1_keeps_named_star (base : Base) (owner field : Acc)
    (e : Excl) (mark : Mark) (demand : Bool) (counted : Acc → Bool)
    (classTag : counted owner = false) (fieldTag : counted field = true) :
    limitF counted 1 ⟨concreteStar base [owner,field] e mark,demand⟩ =
      ⟨concreteStar base [owner,field] e mark,demand⟩ := by
  simp [limitF,cutPath,concreteStar,classTag,fieldTag]

#print axioms field_star_is_candidate
#print axioms field_star_is_rejected_by_old_domain
#print axioms old_domain_in_candidate
#print axioms candidate_rejects_root
#print axioms candidate_rejects_class_wide
#print axioms candidate_rejects_must
#print axioms candidate_rejects_group_actual
#print axioms same_slot_projection_preserves_all_headers
#print axioms same_slot_projection_closed
#print axioms bounded_field_star_relay
#print axioms bounded_field_star_relay_closed
#print axioms overflow_field_relay_is_bounded
#print axioms repeated_bounded_star_relay
#print axioms actual_AP_identity_keeps_concrete_star
#print axioms actual_AP_limit1_keeps_named_star
end RestrictedDemand.StaticInputGrammar
