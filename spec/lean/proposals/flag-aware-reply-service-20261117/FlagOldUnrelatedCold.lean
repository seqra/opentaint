import FlagOldUnrelated
import LayerCold
namespace FlagOldUnrelatedCold
open FlagOldUnrelated NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 65536
set_option maxHeartbeats 320000000

def convert (s : LayerBody.State) : State :=
  ⟨s.rows,s.saved.map (fun n => ⟨n.edge,n.back⟩),s.complete,s.services,
    s.sourceAllowed,s.observationActive,s.report,
    ⟨s.data.domains,s.data.raw,s.data.complete,s.data.services,s.data.offers,s.data.closed⟩⟩
def s0 : State := initial
def s1 : State := convert LayerCold.s1
def s2 : State := convert LayerCold.s2
def s3 : State := convert LayerCold.s3
def s4 : State := convert LayerCold.s4
def s5 : State := convert LayerCold.s5
def s6 : State := convert LayerCold.s6
theorem unchanged_step_1 : step true 1 s0=s1 := by decide +kernel
theorem unchanged_fixed_point_1 : round true 1 (limit 1) s0.rows s0.saved s0.complete s0.services s1.data=s1.data := by decide +kernel
theorem unchanged_step_2 : step true 2 s1=s2 := by decide +kernel
theorem unchanged_fixed_point_2 : round true 2 (limit 2) s1.rows s1.saved s1.complete s1.services s2.data=s2.data := by decide +kernel
theorem unchanged_step_3 : step true 3 s2=s3 := by decide +kernel
theorem unchanged_fixed_point_3 : round true 3 (limit 3) s2.rows s2.saved s2.complete s2.services s3.data=s3.data := by decide +kernel
theorem unchanged_step_4 : step true 4 s3=s4 := by decide +kernel
theorem unchanged_fixed_point_4 : round true 4 (limit 4) s3.rows s3.saved s3.complete s3.services s4.data=s4.data := by decide +kernel
theorem unchanged_step_5 : step true 5 s4=s5 := by decide +kernel
theorem unchanged_fixed_point_5 : round true 5 (limit 5) s4.rows s4.saved s4.complete s4.services s5.data=s5.data := by decide +kernel
theorem unchanged_step_6 : step true 6 s5=s6 := by decide +kernel
theorem unchanged_fixed_point_6 : round true 6 (limit 6) s5.rows s5.saved s5.complete s5.services s6.data=s6.data := by decide +kernel
theorem old_run5_stop_and_observation_are_unchanged : stopped 5 s5=true ∧ s5.report=true := by decide +kernel
end FlagOldUnrelatedCold
