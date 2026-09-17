import Borwein.BulkCandidateData

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Borwein.BulkMomentChunk24
open ComputedMomentTable BulkCandidateData

theorem variance_lower : v[24]!*E*3*64^3 ≤ S*lowerTotal 2 24 := by
  decide +kernel

theorem third_upper : S*upperTotal 3 24 ≤ w3[24]!*E*4*64^4 := by
  decide +kernel

theorem fourth_upper : S*upperTotal 4 24 ≤ w4[24]!*E*5*64^5 := by
  decide +kernel

end Borwein.BulkMomentChunk24
