import RootCleanerPolicy
import OrdinaryCycle

/- The ordinary double-read/double-write helper, with a selected exact-root
   cleaner before its branches. The selected MUST-preserving rule is in force.
   All recurring cleaner inputs have a known nonempty f prefix: the cleaner
   is disjoint, retains their layer, and applies existing survivor protection.
   Concrete protected cuts are outside neutral FLOW/MUST-to-NE coverage. -/
namespace ProtectedCleanerGrowth
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline BoundedLocalRouting BoundedOrdinaryCycle
open NormalUniformNE
set_option linter.unusedSimpArgs false

local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

def full (base n : Nat) (tail : Tail) : Ap := data base n tail (some t)
def source : Offered := ⟨full p 0 .must,false⟩
def sink : Offered := ⟨full ret 0 .may,true⟩
def fRow (n : Nat) (may : Bool := false) : Row :=
  ⟨full p (n+1) (if may then .may else .ne),full ret (n+1) .star⟩
def bRow (n : Nat) (may : Bool := false) : Row :=
  ⟨full ret (n+2) (if may then .may else .ne),full p (n+2) .star⟩
def fQ (n : Nat) : Seed := ⟨full p (n+1) .must,false⟩
def fQ2 (n : Nat) : Seed := ⟨full p (n+2) .star,true⟩
def bQ (n : Nat) : Seed := ⟨full ret (n+2) .star,true⟩
def bQ2 (n : Nat) : Seed := ⟨full ret (n+3) .star,true⟩
def fOffer2 (n : Nat) : Offered := ⟨full p (n+2) .ne,true⟩
def bOffer1 (n : Nat) : Offered := ⟨full ret (n+3) .ne,true⟩

theorem drop_same_fields (n : Nat) : dropHead (fields n) (fields n) = some [] := by
  simpa using drop_fields n 0

/-- Select recurring concrete non-EXACT commands from the complete C2 family.
    Other commands are not disabled in the program or claimed absent. -/
def recurringCommands (run limit : Nat) (backward : Bool) (row : Row) (a : Offered) : List Seed :=
  (emit run limit backward row.entry a).filter fun q =>
    q.ap.mark == some t && q.ap.tail != .exact

theorem source_c2_is_the_concrete_uniform_command (run n : Nat) (may : Bool) :
    recurringCommands run (n+2) false (fRow n may) source = [fQ n] := by
  cases may <;>
    simp [recurringCommands,emit,emitBase,completeFamily,primary,atHead,
      source,fRow,fQ,full,data,selector,marksOK,admits,seed,probe,legalSeed,
      ap,fields_step,dropHead] <;> omega

theorem second_forward_c2_keeps_the_concrete_star_command (run n : Nat) (may : Bool) :
    recurringCommands run (n+2) false (fRow n may) (fOffer2 n) = [fQ2 n] := by
  cases may <;>
    simp [recurringCommands,emit,emitBase,completeFamily,primary,atHead,
      fOffer2,fRow,fQ2,full,data,selector,marksOK,admits,seed,probe,legalSeed,
      ap,drop_fields] <;> omega

theorem first_backward_c2_keeps_the_concrete_star_command (run n : Nat) (may : Bool) :
    recurringCommands run (n+3) true (bRow n may) sink = [bQ n] := by
  have bound : ¬ n+3 < n+1+1 := by omega
  cases may <;>
    simp [recurringCommands,emit,emitBase,completeFamily,primary,atHead,
      sink,bRow,bQ,full,data,selector,marksOK,admits,seed,probe,legalSeed,
      ap,fields_step,dropHead,bound] <;> omega

theorem second_backward_c2_keeps_the_concrete_star_command (run n : Nat) (may : Bool) :
    recurringCommands run (n+3) true (bRow n may) (bOffer1 n) = [bQ2 n] := by
  cases may <;>
    simp [recurringCommands,emit,emitBase,completeFamily,primary,atHead,
      bOffer1,bRow,bQ2,full,data,selector,marksOK,admits,seed,probe,legalSeed,
      ap,drop_fields] <;> omega

/-- Same selected rule as RootCleanerPolicy, rebased from x to helper p. -/
def cleanEntry (c : Value) : Option Value :=
  (UniformRootCleanerPolicy.revisedCleanRoot
    {c with ap := {c.ap with base := UniformRootCleanerCycle.x}}).map fun v =>
      {v with ap := {v.ap with base := p}}

theorem every_nonempty_concrete_input_is_disjoint_and_keeps_its_layer
    (n : Nat) (tail : Tail) (demand flag : Bool) :
    cleanEntry ⟨full p (n+1) tail,demand,flag⟩ =
      some ⟨full p (n+1) tail,demand,true⟩ := by
  simp [cleanEntry,UniformRootCleanerPolicy.revisedCleanRoot,
    UniformRootCleanerCycle.cleanRoot,full,data,ap,fields_step]

theorem root_must_really_uses_the_new_preserving_decision :
    cleanEntry (val (full p 0 .must)) = some {val (full p 0 .must) with h := true} := by decide

def prefixOne (toBase : Nat) (c : Value) : Value :=
  {c with ap := {c.ap with base := toBase,path := f :: c.ap.path}}

theorem prefix_one_is_the_ordinary_known_write_kernel (fromBase toBase : Nat)
    (path : Path) (tail : Tail) :
    moveE fromBase toBase [] [f] (ap fromBase path tail (some t)) =
      some (val (ap toBase (f :: path) tail (some t))) := by
  cases path <;> simp [moveE,move,ap,dropHead,val]

theorem prefix_one_fields (base toBase n : Nat) (tail : Tail) (demand flag : Bool) :
    prefixOne toBase ⟨full base n tail,demand,flag⟩ =
      ⟨full toBase (n+1) tail,demand,flag⟩ := rfl

theorem cut_fields (budget base n : Nat) (tail : Tail) (demand flag : Bool) :
    cut budget ⟨full base n tail,demand,flag⟩ =
      if n > budget then ⟨full base budget .ne,true,flag⟩
      else ⟨full base n tail,demand,flag⟩ := by
  by_cases over : n > budget
  · have le : budget ≤ n := Nat.le_of_lt over
    simp [cut,full,data,ap,fields_length,fields_take,over,Nat.min_eq_left le]
  · simp [cut,full,data,ap,fields_length,over]

/-- Two real one-field operations, with the unchanged global cut after each.
    Support and protection are transported, never reset by the second move. -/
def growTwice (limit toBase : Nat) (c : Value) : Value :=
  cut limit (prefixOne toBase (cut limit (prefixOne 17 c)))

theorem first_growing_uniform_query_is_cut_after_the_second_write (n : Nat) :
    growTwice (n+2) ret ⟨full p (n+1) .must,false,true⟩ =
      ⟨full ret (n+2) .ne,true,true⟩ := by
  simp [growTwice,prefix_one_fields,cut_fields,
    show ¬n+1+1 > n+2 by omega,show n+1+1+1 > n+2 by omega]

theorem at_limit_growing_star_query_is_cut_at_each_write (n : Nat) (base toBase : Nat) :
    growTwice (n+2) toBase ⟨full base (n+2) .star,true,true⟩ =
      ⟨full toBase (n+2) .ne,true,true⟩ := by
  simp [growTwice,prefix_one_fields,cut_fields,show n+2+1 > n+2 by omega]

theorem first_backward_growing_query_is_cut_at_the_second_reverse_read (n : Nat) :
    growTwice (n+3) p ⟨full ret (n+2) .star,true,false⟩ =
      ⟨full p (n+3) .ne,true,false⟩ := by
  simp [growTwice,prefix_one_fields,cut_fields,
    show ¬n+2+1 > n+3 by omega,show n+2+1+1 > n+3 by omega]

def fEdge (n : Nat) : Edge := ((fQ n).ap,⟨full ret (n+2) .ne,true,true⟩)
def fEdge2 (n : Nat) : Edge := ((fQ2 n).ap,⟨full ret (n+2) .ne,true,true⟩)
def bEdge (n : Nat) : Edge := ((bQ n).ap,⟨full p (n+3) .ne,true,true⟩)
def bEdge2 (n : Nat) : Edge := ((bQ2 n).ap,⟨full p (n+3) .ne,true,true⟩)

theorem all_four_cuts_pass_their_own_paired_c5 (n : Nat) (may : Bool) :
    restricted (n+2) [fQ n] (fQ n) (fEdge n).2 (fRow n may) = some (fEdge n) ∧
    restricted (n+2) [fQ2 n] (fQ2 n) (fEdge2 n).2 (fRow n may) = some (fEdge2 n) ∧
    restricted (n+3) [bQ n] (bQ n) (bEdge n).2 (bRow n may) = some (bEdge n) ∧
    restricted (n+3) [bQ2 n] (bQ2 n) (bEdge2 n).2 (bRow n may) = some (bEdge2 n) := by
  cases may <;>
    simp [restricted,fQ,fQ2,bQ,bQ2,fEdge,fEdge2,bEdge,bEdge2,fRow,bRow,
      normalize,normalAp,intersectExit,selector,marksMeet,admits,full,data,ap,cut]

/-- Forward: cleaner, then two ordinary writes. Backward: reverse the two
    field reads, then the same cleaner at the entry point. -/
def growingSummary (limit : Nat) (backward : Bool) (row : Row) (q : Seed) : Option Edge := do
  let start : Value := ⟨q.ap,q.demand,false⟩
  let before ← if backward then some start else cleanEntry start
  let grown := growTwice limit (if backward then p else ret) before
  let after ← if backward then cleanEntry grown else some grown
  restricted limit [q] q after row

theorem all_four_edges_are_generated_by_the_actual_growing_branch (n : Nat) (may : Bool) :
    growingSummary (n+2) false (fRow n may) (fQ n) = some (fEdge n) ∧
    growingSummary (n+2) false (fRow n may) (fQ2 n) = some (fEdge2 n) ∧
    growingSummary (n+3) true (bRow n may) (bQ n) = some (bEdge n) ∧
    growingSummary (n+3) true (bRow n may) (bQ2 n) = some (bEdge2 n) := by
  have cleaner1 := every_nonempty_concrete_input_is_disjoint_and_keeps_its_layer n .must false false
  have cleaner2 := every_nonempty_concrete_input_is_disjoint_and_keeps_its_layer (n+1) .star true false
  have cleaner3 := every_nonempty_concrete_input_is_disjoint_and_keeps_its_layer (n+2) .ne true false
  have cleaner4 := every_nonempty_concrete_input_is_disjoint_and_keeps_its_layer (n+2) .ne true true
  rcases all_four_cuts_pass_their_own_paired_c5 n may with ⟨a,b,c,d⟩
  constructor
  · simpa [growingSummary,fQ,first_growing_uniform_query_is_cut_after_the_second_write,cleaner1,fEdge] using a
  constructor
  · simpa [growingSummary,fQ2,at_limit_growing_star_query_is_cut_at_each_write,cleaner2,fEdge2] using b
  constructor
  · simpa [growingSummary,bQ,first_backward_growing_query_is_cut_at_the_second_reverse_read,cleaner3,bEdge] using c
  · -- The input is not protected until it reaches the entry cleaner.
    have growPlain : growTwice (n+3) p ⟨full ret (n+3) .star,true,false⟩ =
        ⟨full p (n+3) .ne,true,false⟩ := by
      simp [growTwice,prefix_one_fields,cut_fields,show n+3+1 > n+3 by omega]
    simpa [growingSummary,bQ2,growPlain,cleaner3,bEdge2] using d

theorem every_uniform_ne_provider_rejects_these_protected_cuts (normal : Edge) (n : Nat) :
    uniformCovers normal (fEdge n) = false ∧ uniformCovers normal (fEdge2 n) = false ∧
    uniformCovers normal (bEdge n) = false ∧ uniformCovers normal (bEdge2 n) = false := by
  exact ⟨protected_ne_is_never_removed _ _ rfl,protected_ne_is_never_removed _ _ rfl,
    protected_ne_is_never_removed _ _ rfl,protected_ne_is_never_removed _ _ rfl⟩

theorem concrete_origin_alone_is_outside_uniform_flow_coverage (normal : Edge) (n : Nat) :
    uniformCovers normal ((fEdge n).1,{(fEdge n).2 with h := false}) = false := by
  simp [uniformCovers,fEdge,fQ,full,data,ap]

theorem a_protected_witness_survives_the_complete_uniform_compaction
    (all : List Edge) (edge : Edge) (inside : edge ∈ all) (flag : edge.2.h = true) :
    edge ∈ compact true all := by
  have noCover : ∀ normal, uniformCovers normal edge = false :=
    fun normal => protected_ne_is_never_removed normal edge flag
  simp [compact,inside,noCover]

end ProtectedCleanerGrowth

#print axioms ProtectedCleanerGrowth.source_c2_is_the_concrete_uniform_command
#print axioms ProtectedCleanerGrowth.drop_same_fields
#print axioms ProtectedCleanerGrowth.second_forward_c2_keeps_the_concrete_star_command
#print axioms ProtectedCleanerGrowth.first_backward_c2_keeps_the_concrete_star_command
#print axioms ProtectedCleanerGrowth.second_backward_c2_keeps_the_concrete_star_command
#print axioms ProtectedCleanerGrowth.every_nonempty_concrete_input_is_disjoint_and_keeps_its_layer
#print axioms ProtectedCleanerGrowth.root_must_really_uses_the_new_preserving_decision
#print axioms ProtectedCleanerGrowth.prefix_one_is_the_ordinary_known_write_kernel
#print axioms ProtectedCleanerGrowth.prefix_one_fields
#print axioms ProtectedCleanerGrowth.cut_fields
#print axioms ProtectedCleanerGrowth.first_growing_uniform_query_is_cut_after_the_second_write
#print axioms ProtectedCleanerGrowth.at_limit_growing_star_query_is_cut_at_each_write
#print axioms ProtectedCleanerGrowth.first_backward_growing_query_is_cut_at_the_second_reverse_read
#print axioms ProtectedCleanerGrowth.all_four_cuts_pass_their_own_paired_c5
#print axioms ProtectedCleanerGrowth.all_four_edges_are_generated_by_the_actual_growing_branch
#print axioms ProtectedCleanerGrowth.every_uniform_ne_provider_rejects_these_protected_cuts
#print axioms ProtectedCleanerGrowth.concrete_origin_alone_is_outside_uniform_flow_coverage
#print axioms ProtectedCleanerGrowth.a_protected_witness_survives_the_complete_uniform_compaction
