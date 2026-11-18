import BoundFamilyCases
namespace BoundFamilyBatch4
open BoundFamilyCases
set_option maxRecDepth 65536
set_option maxHeartbeats 640000000

theorem finite_family_naturally_stops_and_keeps_observations :
    (chunk 4).all checked=true := by decide +kernel
end BoundFamilyBatch4
