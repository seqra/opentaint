import Closure

namespace UniformNERegressions
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline BoundedLocalRouting BoundedOrdinaryCycle
open NormalUniformNE UniformNEClosure

local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

def readBBRow : Row := ⟨data p 1 .ne,data ret 0 .star⟩
def readBBActual : Offered := ⟨data p 1 .must,false⟩

def readBB : List Edge :=
  let seeds := emit 3 2 false readBBRow.entry readBBActual
  seeds.flatMap fun q =>
    (moveE p ret [f,g] [] q.ap).toList.filterMap fun c =>
      restricted 2 seeds q (cut 2 c) readBBRow

def bbBody (q : Ap) : List Value :=
  -- Current readBB result; persisted NORMAL writeBB result first.
  [readBB.head?.bind fun e => (normalApply e ⟨q,false⟩).map fun v => val v.ap v.demand,
   (normalApply normalWriter ⟨q,false⟩).map fun v => val v.ap v.demand].filterMap id

def bbPacket : List Edge :=
  oldRows3.flatMap fun row =>
    let commands := plan 3 2 false row fieldUniform
    let seeds := commands.map Command.seed
    commands.flatMap fun command =>
      (bbBody command.seed.ap).filterMap fun raw =>
        if raw.ap.path.length ≤ 2 && writerCovered oldProgram command.seed.ap raw then none
        else restricted 2 seeds command.seed (cut 2 raw) row

theorem the_read_block_is_admitted_and_publishes_a_normal_uniform_reader :
    readBB = [(data p 1 .must,val (data ret 0 .must))] := by decide

theorem neither_inner_block_produces_demand_in_the_closed_run3 :
    (bbBody (data p 1 .must)).any Value.demand = false ∧
    readBB.any (fun e => e.2.demand) = false := by decide

theorem the_bb_method_packet_is_the_complete_old_method_packet :
    bbPacket = oldPacket := by decide

theorem the_bb_method_and_all_inner_blocks_finish_without_demand :
    handoff ((compact true bbPacket).eraseDups) = [] ∧
    handoff readBB = [] ∧ rootDemand oldSecond = false ∧
    confirmed oldSecond = true := by decide

theorem old_current_initial_families_are_only_f_uniform :
    (oldRows3.flatMap fun row => (plan 3 2 false row fieldUniform).map Command.seed).all
      (fun q => decide (q.ap = data p 1 .must)) = true ∧
    (oldRows3.flatMap fun row => (plan 3 2 false row rootUniform).map Command.seed).all
      (fun q => decide (q.ap = data p 1 .must)) = true := by decide

theorem longer_readers_have_the_same_normal_result_without_unfolding (rest : Path) :
    moveE p ret ([f,g] ++ rest) [] (data p 1 .must) =
      some (val (data ret 0 .must)) := by
  exact uniform_reader_does_not_need_the_full_read_prefix rest

theorem the_complete_longer_reader_packet_is_unchanged (rest : Path) :
    ownerRun3 ⟨[f,g] ++ rest,[f]⟩ oldRows3 fieldUniform = oldPacket := by
  have rows : oldRows3 =
      [⟨data p 1 .ne,data ret 0 .star⟩,
       ⟨data p 1 .ne,data ret 1 .star⟩] := by decide
  simp [oldPacket,ownerRun3,rows,plan,emit,emitBase,completeFamily,primary,
    atHead,selector,marksOK,admits,seed,probe,legalSeed,fieldUniform,
    data,fields,ap,p,ret,t,f,g,dropHead,moveE,move,oldProgram,writerCovered,
    List.eraseDups_cons,List.eraseDups_nil,val]

def cleanerDemand : Ap := data ret 0 .may (some t)
def cleanerActual : Offered := ⟨data ret 0 .may (some t),true⟩
def cleanerQueries := emit 2 1 true cleanerDemand cleanerActual

def rootCleaner (q : Seed) : List Edge :=
  if q.ap.mark == some t then
    if q.ap.path.isEmpty && q.ap.tail == .exact then []
    else if q.ap.path.isEmpty && q.ap.tail == .star then
      [(q.ap,{val (data p 0 .may (some t)) true with h := true})]
    else [(q.ap,val {q.ap with base := p} q.demand)]
  else []
def cleanerPacket := cleanerQueries.flatMap rootCleaner

theorem the_cleaner_keeps_its_nonempty_concrete_repair :
    cleanerPacket =
      [(data ret 0 .star (some t),
        {val (data p 0 .may (some t)) true with h := true})] ∧
    compact true cleanerPacket = cleanerPacket := by decide

theorem the_repair_overlaps_the_real_exact_field_source :
    (cleanerPacket.head?.bind fun e =>
      applyLoss e ⟨data ret 0 .may (some t),true⟩).isSome = true ∧
    emit 3 2 false (data p 0 .may (some t))
      ⟨data p 1 .exact (some t),false⟩ =
      [⟨data p 1 .exact (some t),false⟩,⟨data p 0 .exact,false⟩] := by decide

theorem the_precise_descendant_survives_and_can_report_normally :
    rootCleaner ⟨data ret 1 .exact (some t),false⟩ =
      [(data ret 1 .exact (some t),val (data p 1 .exact (some t)))] := by decide

def cleanerForwardRow : Row := ⟨data p 0 .may (some t),data ret 0 .star (some t)⟩
def cleanerForwardPacket : List Edge :=
  let actual : Offered := ⟨data p 1 .exact (some t),false⟩
  let seeds := emit 3 2 false cleanerForwardRow.entry actual
  seeds.filterMap fun q =>
    if q.ap.mark == some t && !q.ap.path.isEmpty then
      restricted 2 seeds q (val {q.ap with base := ret} q.demand) cleanerForwardRow
    else none -- FLOW companion excludes T; exact root was cleaned.

theorem the_cleaner_concrete_run3_frontier_is_empty_with_a_normal_survivor :
    compact true cleanerForwardPacket =
      [(data p 1 .exact (some t),val (data ret 1 .exact (some t)))] ∧
    handoff cleanerForwardPacket = [] := by decide

theorem the_wrapper_child_query_and_h_reader_are_unchanged :
    compact true [(childExact.seed.ap,val (ap p [3] .exact))] =
      [(childExact.seed.ap,val (ap p [3] .exact))] ∧
    moveE p ret [3] [f] (ap p [3] .must (some t)) =
      some (val (ap ret [f] .must (some t))) := by decide

def wrapperRow : Row := ⟨ap p [3] .may,ap ret [4] .star⟩
def wrapperActual : Offered := ⟨ap p [3] .must (some t),false⟩
def wrapperPacket : List Edge :=
  let seeds := emit 3 2 false wrapperRow.entry wrapperActual
  seeds.filterMap fun q => do
    let fromChild ← moveE p ret [3] [f] q.ap
    let wrapped ← moveE ret ret [] [4] fromChild.ap
    restricted 2 seeds q wrapped wrapperRow

theorem the_wrapper_finding_route_is_a_legal_normal_run3_summary :
    wrapperPacket =
      [(ap p [3] .must,val (ap ret [4,f] .must))] ∧
    compact true wrapperPacket = wrapperPacket ∧
    (wrapperPacket.head?.bind fun e => normalApply e wrapperActual) =
      some ⟨ap ret [4,f] .must (some t),false⟩ := by decide

theorem weak_reverse_uniform_records_are_not_reclassified_normal :
    compact false [(data ret 0 .star,val (data p 1 .may) true)] =
      [(data ret 0 .star,val (data p 1 .may) true)] := rfl

end UniformNERegressions

#print axioms UniformNERegressions.the_read_block_is_admitted_and_publishes_a_normal_uniform_reader
#print axioms UniformNERegressions.neither_inner_block_produces_demand_in_the_closed_run3
#print axioms UniformNERegressions.the_bb_method_packet_is_the_complete_old_method_packet
#print axioms UniformNERegressions.the_bb_method_and_all_inner_blocks_finish_without_demand
#print axioms UniformNERegressions.old_current_initial_families_are_only_f_uniform
#print axioms UniformNERegressions.longer_readers_have_the_same_normal_result_without_unfolding
#print axioms UniformNERegressions.the_complete_longer_reader_packet_is_unchanged
#print axioms UniformNERegressions.the_cleaner_keeps_its_nonempty_concrete_repair
#print axioms UniformNERegressions.the_repair_overlaps_the_real_exact_field_source
#print axioms UniformNERegressions.the_precise_descendant_survives_and_can_report_normally
#print axioms UniformNERegressions.the_cleaner_concrete_run3_frontier_is_empty_with_a_normal_survivor
#print axioms UniformNERegressions.the_wrapper_child_query_and_h_reader_are_unchanged
#print axioms UniformNERegressions.the_wrapper_finding_route_is_a_legal_normal_run3_summary
#print axioms UniformNERegressions.weak_reverse_uniform_records_are_not_reclassified_normal
