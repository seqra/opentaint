import NestedWriteCold
namespace NestedWriteBodies
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle BoundedRefinementPipeline NormalUniformNE
open NestedSavedReplayCycle NestedColdMachine OverwriteReplay NestedWriteReplay
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 80000000
local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

theorem bodyFE0 (k : Nat) :
    (NestedWriteReplay.body (2*k+5) (2*k+4) [] [] (NestedWriteCold.methods[0]!)[0]!
      ⟨point p [] .exact,false⟩ [] [] ⟨[],[],[]⟩).2 =
    (NestedWriteReplay.body 5 4 [] [] (NestedWriteCold.methods[0]!)[0]!
      ⟨point p [] .exact,false⟩ [] [] ⟨[],[],[]⟩).2 := by
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

theorem bodyFE1 (k : Nat) :
    (NestedWriteReplay.body (2*k+5) (2*k+4) [] [] (NestedWriteCold.methods[0]!)[1]!
      ⟨point p [] .exact,false⟩ [] [] ⟨[],[],[]⟩).2 =
    (NestedWriteReplay.body 5 4 [] [] (NestedWriteCold.methods[0]!)[1]!
      ⟨point p [] .exact,false⟩ [] [] ⟨[],[],[]⟩).2 := by
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

theorem bodyFG0 (k : Nat) :
    (NestedWriteReplay.body (2*k+5) (2*k+4) [] [] (NestedWriteCold.methods[0]!)[0]!
      ⟨point p [g] .star,false⟩ [] [] ⟨[],[],[]⟩).2 =
    (NestedWriteReplay.body 5 4 [] [] (NestedWriteCold.methods[0]!)[0]!
      ⟨point p [g] .star,false⟩ [] [] ⟨[],[],[]⟩).2 := by
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

theorem bodyFG1 (k : Nat) :
    (NestedWriteReplay.body (2*k+5) (2*k+4) [] [] (NestedWriteCold.methods[0]!)[1]!
      ⟨point p [g] .star,false⟩ [] [] ⟨[],[],[]⟩).2 =
    (NestedWriteReplay.body 5 4 [] [] (NestedWriteCold.methods[0]!)[1]!
      ⟨point p [g] .star,false⟩ [] [] ⟨[],[],[]⟩).2 := by
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

theorem bodyBE0 (k : Nat) :
    (NestedWriteReplay.body (2*k+6) (2*k+5) [] [] (NestedWriteCold.methods[0]!)[0]!
      ⟨point p [] .exact,false⟩ [] [] ⟨[],[],[]⟩).2 =
    (NestedWriteReplay.body 6 5 [] [] (NestedWriteCold.methods[0]!)[0]!
      ⟨point p [] .exact,false⟩ [] [] ⟨[],[],[]⟩).2 := by
  have l0 : ¬2*k+5<0 := by omega
  have l1 : ¬2*k+5<1 := by omega
  have l2 : ¬2*k+5<2 := by omega
  have l3 : ¬2*k+5<3 := by omega
  have nr : 2*k+6 ≠ 1 := by omega
  have par : (2*k+6)%2 = 0 := by omega
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

theorem bodyBE1 (k : Nat) :
    (NestedWriteReplay.body (2*k+6) (2*k+5) [] [] (NestedWriteCold.methods[0]!)[1]!
      ⟨point p [] .exact,false⟩ [] [] ⟨[],[],[]⟩).2 =
    (NestedWriteReplay.body 6 5 [] [] (NestedWriteCold.methods[0]!)[1]!
      ⟨point p [] .exact,false⟩ [] [] ⟨[],[],[]⟩).2 := by
  have l0 : ¬2*k+5<0 := by omega
  have l1 : ¬2*k+5<1 := by omega
  have l2 : ¬2*k+5<2 := by omega
  have l3 : ¬2*k+5<3 := by omega
  have nr : 2*k+6 ≠ 1 := by omega
  have par : (2*k+6)%2 = 0 := by omega
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

theorem bodyBS0 (k : Nat) :
    (NestedWriteReplay.body (2*k+6) (2*k+5) [] [] (NestedWriteCold.methods[0]!)[0]!
      ⟨point p [] .star,false⟩ [f] [] ⟨[],[],[]⟩).2 =
    (NestedWriteReplay.body 6 5 [] [] (NestedWriteCold.methods[0]!)[0]!
      ⟨point p [] .star,false⟩ [f] [] ⟨[],[],[]⟩).2 := by
  have l0 : ¬2*k+5<0 := by omega
  have l1 : ¬2*k+5<1 := by omega
  have l2 : ¬2*k+5<2 := by omega
  have l3 : ¬2*k+5<3 := by omega
  have nr : 2*k+6 ≠ 1 := by omega
  have par : (2*k+6)%2 = 0 := by omega
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

theorem bodyBS1 (k : Nat) :
    (NestedWriteReplay.body (2*k+6) (2*k+5) [] [] (NestedWriteCold.methods[0]!)[1]!
      ⟨point p [] .star,false⟩ [f] [] ⟨[],[],[]⟩).2 =
    (NestedWriteReplay.body 6 5 [] [] (NestedWriteCold.methods[0]!)[1]!
      ⟨point p [] .star,false⟩ [f] [] ⟨[],[],[]⟩).2 := by
  have l0 : ¬2*k+5<0 := by omega
  have l1 : ¬2*k+5<1 := by omega
  have l2 : ¬2*k+5<2 := by omega
  have l3 : ¬2*k+5<3 := by omega
  have nr : 2*k+6 ≠ 1 := by omega
  have par : (2*k+6)%2 = 0 := by omega
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

theorem bodyBFE0 (k : Nat) :
    (NestedWriteReplay.body (2*k+6) (2*k+5) [] [] (NestedWriteCold.methods[0]!)[0]!
      ⟨point p [f] .exact,false⟩ [] [] ⟨[],[],[]⟩).2 =
    (NestedWriteReplay.body 6 5 [] [] (NestedWriteCold.methods[0]!)[0]!
      ⟨point p [f] .exact,false⟩ [] [] ⟨[],[],[]⟩).2 := by
  have l0 : ¬2*k+5<0 := by omega
  have l1 : ¬2*k+5<1 := by omega
  have l2 : ¬2*k+5<2 := by omega
  have l3 : ¬2*k+5<3 := by omega
  have nr : 2*k+6 ≠ 1 := by omega
  have par : (2*k+6)%2 = 0 := by omega
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

theorem bodyBFE1 (k : Nat) :
    (NestedWriteReplay.body (2*k+6) (2*k+5) [] [] (NestedWriteCold.methods[0]!)[1]!
      ⟨point p [f] .exact,false⟩ [] [] ⟨[],[],[]⟩).2 =
    (NestedWriteReplay.body 6 5 [] [] (NestedWriteCold.methods[0]!)[1]!
      ⟨point p [f] .exact,false⟩ [] [] ⟨[],[],[]⟩).2 := by
  have l0 : ¬2*k+5<0 := by omega
  have l1 : ¬2*k+5<1 := by omega
  have l2 : ¬2*k+5<2 := by omega
  have l3 : ¬2*k+5<3 := by omega
  have nr : 2*k+6 ≠ 1 := by omega
  have par : (2*k+6)%2 = 0 := by omega
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

theorem bodyBFS0 (k : Nat) :
    (NestedWriteReplay.body (2*k+6) (2*k+5) [] [] (NestedWriteCold.methods[0]!)[0]!
      ⟨point p [f] .star,false⟩ [] [] ⟨[],[],[]⟩).2 =
    (NestedWriteReplay.body 6 5 [] [] (NestedWriteCold.methods[0]!)[0]!
      ⟨point p [f] .star,false⟩ [] [] ⟨[],[],[]⟩).2 := by
  have l0 : ¬2*k+5<0 := by omega
  have l1 : ¬2*k+5<1 := by omega
  have l2 : ¬2*k+5<2 := by omega
  have l3 : ¬2*k+5<3 := by omega
  have nr : 2*k+6 ≠ 1 := by omega
  have par : (2*k+6)%2 = 0 := by omega
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

theorem bodyBFS1 (k : Nat) :
    (NestedWriteReplay.body (2*k+6) (2*k+5) [] [] (NestedWriteCold.methods[0]!)[1]!
      ⟨point p [f] .star,false⟩ [] [] ⟨[],[],[]⟩).2 =
    (NestedWriteReplay.body 6 5 [] [] (NestedWriteCold.methods[0]!)[1]!
      ⟨point p [f] .star,false⟩ [] [] ⟨[],[],[]⟩).2 := by
  have l0 : ¬2*k+5<0 := by omega
  have l1 : ¬2*k+5<1 := by omega
  have l2 : ¬2*k+5<2 := by omega
  have l3 : ¬2*k+5<3 := by omega
  have nr : 2*k+6 ≠ 1 := by omega
  have par : (2*k+6)%2 = 0 := by omega
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

end NestedWriteBodies
#print axioms NestedWriteBodies.bodyFE0
#print axioms NestedWriteBodies.bodyFE1
#print axioms NestedWriteBodies.bodyFG0
#print axioms NestedWriteBodies.bodyFG1
#print axioms NestedWriteBodies.bodyBE0
#print axioms NestedWriteBodies.bodyBE1
#print axioms NestedWriteBodies.bodyBS0
#print axioms NestedWriteBodies.bodyBS1
#print axioms NestedWriteBodies.bodyBFE0
#print axioms NestedWriteBodies.bodyBFE1
#print axioms NestedWriteBodies.bodyBFS0
#print axioms NestedWriteBodies.bodyBFS1
