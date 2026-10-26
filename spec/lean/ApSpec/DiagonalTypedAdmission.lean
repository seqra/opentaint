/- Narrow implementation correspondence repair for selected typed admission.
   This module does not change FLOW-versus-TAINT replacement or the AP denotation.
   The Kotlin adapter reuses TaintGroup; these laws justify its cross-header cells. -/
import ApSpec.CorrelatedConcreteImplementation
import ApSpec.Subsume

namespace ApSpec.DiagonalTypedAdmission
open ApSpec ApSpec.Run1CorrelatedConcreteInitials

/-- ANY at an output prefix contains a correlated STAR result for the same
    complete initial and atom. The input suffix remains the original witness. -/
theorem any_covers_star_prefix (i : PFact) (b : Base) (q extra : List Acc)
    (e : Excl) (m : MarkA) (x y : Loc)
    (h : den i ⟨b,q ++ extra,.star e,m⟩ x y) :
    den i ⟨b,q,.any,m⟩ x y := by
  obtain ⟨b0,b1,m0,m1,pass,s,r,p0,p1,hi,_⟩ := h
  refine ⟨b0,b1,m0,m1,pass,s,extra ++ r,p0,?_,hi,trivial⟩
  simpa [List.append_assoc] using p1

/-- Equal-path STAR coverage admits every suffix of the offered E cell.
    A proper STAR prefix is deliberately not used here. -/
theorem star_covers_star (i : PFact) (b : Base) (q : List Acc)
    (stored offered : Excl) (m : MarkA) (less : stored.subB offered = true)
    (x y : Loc) (h : den i ⟨b,q,.star offered,m⟩ x y) :
    den i ⟨b,q,.star stored,m⟩ x y := by
  obtain ⟨b0,b1,m0,m1,pass,s,r,p0,p1,hi,eq,admitted⟩ := h
  exact ⟨b0,b1,m0,m1,pass,s,r,p0,p1,hi,eq,CoreAux.Excl.subB_sound less admitted⟩

/-- Removing the covered later offer keeps the exact represented pair union.
    This is not authority to remove previously stored STAR rows after ANY. -/
theorem covered_later_star_union (i : PFact) (b : Base) (q extra : List Acc)
    (e : Excl) (m : MarkA) (x y : Loc) :
    (den i ⟨b,q,.any,m⟩ x y ∨ den i ⟨b,q ++ extra,.star e,m⟩ x y) ↔
    den i ⟨b,q,.any,m⟩ x y :=
  remove_covered_relation i _ i _ (fun x y h => any_covers_star_prefix i b q extra e m x y h) x y

/-- The existing equal-root exclusion intersection is exact. This repair
    reuses it; it introduces no new exclusion policy or layer promotion. -/
theorem equal_root_exclusion_merge (i : PFact) (b : Base) (q : List Acc)
    (e1 e2 : Excl) (m : MarkA) (x y : Loc) :
    den i ⟨b,q,.star (e1.inter e2),m⟩ x y ↔
      den i ⟨b,q,.star e1,m⟩ x y ∨ den i ⟨b,q,.star e2,m⟩ x y :=
  Subsume.merge_inter

/-- At each represented relation membership, ordinary and protected novelty
    are separate. A plain covering row cannot consume a new protected guide. -/
structure Bits where
  ordinary : Bool
  protectedBit : Bool
deriving DecidableEq, Repr

def delta (stored offered : Bits) : Bits :=
  let fresh := offered.ordinary && !stored.ordinary
  let flagged := offered.protectedBit && !stored.protectedBit
  ⟨fresh || flagged,flagged⟩

def accept (stored offered : Bits) : Bits :=
  ⟨stored.ordinary || offered.ordinary,stored.protectedBit || offered.protectedBit⟩

theorem covered_plain_no_delta (p : Bool) : delta ⟨true,p⟩ ⟨true,false⟩ = ⟨false,false⟩ := by
  cases p <;> rfl

theorem covered_protected_no_delta : delta ⟨true,true⟩ ⟨true,true⟩ = ⟨false,false⟩ := rfl

theorem late_protection_is_work : delta ⟨true,false⟩ ⟨true,true⟩ = ⟨true,true⟩ := rfl

theorem unchanged_repeat_no_delta (stored offered : Bits) :
    delta (accept stored offered) offered = ⟨false,false⟩ := by
  cases stored with | mk so sp =>
    cases offered with | mk oo op =>
      cases so <;> cases sp <;> cases oo <;> cases op <;> rfl

theorem protected_obligation_retained (stored offered : Bits)
    (supplied : offered.protectedBit = true) : (accept stored offered).protectedBit = true := by
  simp [accept,supplied]

/-- Handoff maps STAR output regions to ANY. A retained prefix ANY guide
    covers each removed descendant guide; the complete opposite endpoint
    and the atom are equal by the Kotlin scope/diagonal checks. -/
theorem handoff_any_prefix (b : Base) (q extra : List Acc) (m : MarkA) (l : Loc)
    (h : (PFact.mk b (q ++ extra) .any m).covers l) :
    (PFact.mk b q .any m).covers l := by
  obtain ⟨hb,⟨s,hp,_⟩,hm⟩ := h
  refine ⟨hb,⟨extra ++ s,?_,trivial⟩,hm⟩
  simpa [List.append_assoc] using hp

#print axioms any_covers_star_prefix
#print axioms star_covers_star
#print axioms covered_later_star_union
#print axioms equal_root_exclusion_merge
#print axioms unchanged_repeat_no_delta
#print axioms protected_obligation_retained
#print axioms handoff_any_prefix
end ApSpec.DiagonalTypedAdmission
