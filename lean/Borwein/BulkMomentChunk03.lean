import Borwein.BulkCandidateData

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Borwein.BulkMomentChunk03
open ComputedMomentTable BulkCandidateData

theorem variance_lower : v[3]!*E*3*64^3 ≤ S*lowerTotal 2 3 := by
  decide +kernel

theorem third_upper : S*upperTotal 3 3 ≤ w3[3]!*E*4*64^4 := by
  decide +kernel

theorem fourth_upper : S*upperTotal 4 3 ≤ w4[3]!*E*5*64^5 := by
  decide +kernel

end Borwein.BulkMomentChunk03
