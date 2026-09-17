import Borwein.BulkCandidateData

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Borwein.BulkMomentChunk01
open ComputedMomentTable BulkCandidateData

theorem variance_lower : v[1]!*E*3*64^3 ≤ S*lowerTotal 2 1 := by
  decide +kernel

theorem third_upper : S*upperTotal 3 1 ≤ w3[1]!*E*4*64^4 := by
  decide +kernel

theorem fourth_upper : S*upperTotal 4 1 ≤ w4[1]!*E*5*64^5 := by
  decide +kernel

end Borwein.BulkMomentChunk01
