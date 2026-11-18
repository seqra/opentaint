import LostMarkOrigin
namespace OriginGrowth
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
set_option maxHeartbeats 16000000

def source : Value:=val (ap p [] .exact (some t))
def write (k : Nat) (c : Value) : Value:=cut k {c with ap:={c.ap with path:=f::c.ap.path}}
def grow (k : Nat) : Nat → Value
 | 0=>source
 | n+1=>write k (grow k n)
def observed (k : Nat) : Option Value:=LostMarkOrigin.readThree (grow k 4)

theorem a_NORMAL_marking_activation_can_still_have_only_DEMAND_observation :
    source.demand=false ∧
    observed 1=some (val (ap p [] .may (some t)) true) ∧
    observed 2=some (val (ap p [] .may (some t)) true) := by decide
theorem the_later_precise_route_is_real :
    observed 4=some (val (ap p [f] .exact (some t))) := by decide
end OriginGrowth
