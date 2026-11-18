import NestedWriteBodies

namespace NestedWriteConcrete
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE
open NestedSavedReplayCycle NestedColdMachine OverwriteReplay NestedWriteReplay
set_option maxRecDepth 16384
set_option maxHeartbeats 80000000
set_option linter.unusedSimpArgs false
local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

/-- Exact marked points only: ordinary overwrite removes its subtree;
    assignment/read transports the surviving exact suffix. -/
def concreteStep (op : NestedWriteReplay.Op) (word : Path) : Option Path :=
  match op with
  | .nestedWrite written => if (dropHead written word).isSome then none else some word
  | .overwrite field => if (dropHead [field] word).isSome then none else some word
  | .move read write => (dropHead read word).map (write ++ ·)
def concreteRun : List NestedWriteReplay.Op → Path → Option Path
  | [],word => some word
  | op :: rest,word => (concreteStep op word).bind (concreteRun rest)

theorem marked_g_region_has_no_return_in_reader (suffix : Path) :
    concreteRun (NestedWriteCold.methods[0]!)[0]! ([g] ++ suffix) = none := by
  simp [concreteRun,concreteStep,NestedWriteCold.methods,dropHead,f,g]

theorem marked_g_region_has_no_return_in_writer (suffix : Path) :
    concreteRun (NestedWriteCold.methods[0]!)[1]! ([g] ++ suffix) = none := by
  simp [concreteRun,concreteStep,NestedWriteCold.methods,dropHead,f,g]

theorem root_exact_write_keep_creates_may_without_a_read (k : Nat) :
    keep (k+2) [f] g (val (point p [] .exact)) =
      some (val (point p [f] .may) true) := by rfl

theorem ordinary_read_of_root_exact_cannot_do_that :
    OverwriteReplay.move [f] [] (point p [] .exact) = none := by decide

theorem current_child_routing_does_not_cover_exact_probe (mask : List Nat) :
    ExclusionChildReplay.eligible (point p [] .exact) mask
      (point p [f] .star,val (point ret [] .star)) true
      ⟨point p [] .exact,false⟩ = false := by
  simp [ExclusionChildReplay.eligible,point,ap]

theorem any_child_mask_keeps_the_exact_probe_may (k : Nat) (mask : List Nat) :
    (NestedWriteReplay.body (2*k+5) (2*k+4) [] [] (NestedWriteCold.methods[0]!)[0]!
      ⟨point p [] .exact,false⟩ mask [] ⟨[],[],[]⟩).2 =
      [val (point ret [] .may) true] := by
  have l0 : ¬2*k+4<0 := by omega
  have l1 : ¬2*k+4<1 := by omega
  have l2 : ¬2*k+4<2 := by omega
  have l3 : ¬2*k+4<3 := by omega
  have nr : 2*k+5 ≠ 1 := by omega
  have par : (2*k+5)%2 = 1 := by omega
  dsimp only [NestedWriteReplay.body,NestedWriteCold.methods]
  simp only [par,Bool.false_eq_true,ite_false,ite_true]
  dsimp only [NestedWriteReplay.reversed,NestedWriteReplay.through,NestedWriteReplay.step]
  simp [NestedWriteReplay.body,NestedWriteCold.methods,NestedWriteReplay.reversed,
    NestedWriteReplay.through,NestedWriteReplay.step,NestedWriteReplay.nestedWrite,NestedWriteReplay.keep,
    OverwriteReplay.values,OverwriteReplay.valueCovered,OverwriteReplay.valueKey,OverwriteReplay.apKey,
    OverwriteReplay.move,OverwriteReplay.union,normalAp,point,ap,admits,dropHead,sortBy,insertBy,unique,
    NestedColdMachine.apKey,NestedColdMachine.pathKey,NestedColdMachine.tailKey,p,ret,f,g,cut,val,
    List.eraseDups,List.eraseDupsBy,List.eraseDupsBy.loop,List.getElem!_eq_getElem?_getD,
    l0,l1,l2,l3,nr,par,NonEmptyPolicy.instBEqOffered.beq,
    NonEmptyPolicy.instBEqAp.beq,NonEmptyPolicy.instBEqTail.beq,NonEmptyPolicy.Tail.ctorIdx,
    Option.instBEq.beq,List.beq,BEq.beq]


theorem no_saved_normal_packet_hides_this_demand (k : Nat) (norms : List (Edge × Bool)) :
    OverwriteReplay.pub (k+2) (k+1) norms
      ⟨point p [] .may,point ret [] .star⟩ [⟨point p [] .exact,false⟩]
      ⟨point p [] .exact,false⟩ (val (point ret [] .may) true) =
      some (point p [] .star,val (point ret [] .may) true) := by
  have nr : k+2 ≠ 1 := by omega
  have l1 : 1 ≤ k+1 := by omega
  simp [OverwriteReplay.pub,OverwriteReplay.normalsCover,BoundedRefinementPipeline.restricted,normalize,
    intersectExit,selector,marksMeet,normalAp,point,ap,val,cut,nr,l1,p,ret]

end NestedWriteConcrete
#print axioms NestedWriteConcrete.marked_g_region_has_no_return_in_reader
#print axioms NestedWriteConcrete.marked_g_region_has_no_return_in_writer
#print axioms NestedWriteConcrete.root_exact_write_keep_creates_may_without_a_read
#print axioms NestedWriteConcrete.ordinary_read_of_root_exact_cannot_do_that
#print axioms NestedWriteConcrete.current_child_routing_does_not_cover_exact_probe

#print axioms NestedWriteConcrete.any_child_mask_keeps_the_exact_probe_may
#print axioms NestedWriteConcrete.no_saved_normal_packet_hides_this_demand
