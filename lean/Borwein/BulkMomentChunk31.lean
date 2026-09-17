import Borwein.BulkCandidateData

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Borwein.BulkMomentChunk31
open ComputedMomentTable BulkCandidateData

theorem variance_lower : v[31]!*E*3*64^3 ≤ S*lowerTotal 2 31 := by
  decide +kernel

theorem third_upper : S*upperTotal 3 31 ≤ w3[31]!*E*4*64^4 := by
  decide +kernel

theorem fourth_upper : S*upperTotal 4 31 ≤ w4[31]!*E*5*64^5 := by
  decide +kernel

end Borwein.BulkMomentChunk31
