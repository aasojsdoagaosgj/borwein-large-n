import Borwein.BulkCandidateData

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Borwein.BulkMomentChunk28
open ComputedMomentTable BulkCandidateData

theorem variance_lower : v[28]!*E*3*64^3 ≤ S*lowerTotal 2 28 := by
  decide +kernel

theorem third_upper : S*upperTotal 3 28 ≤ w3[28]!*E*4*64^4 := by
  decide +kernel

theorem fourth_upper : S*upperTotal 4 28 ≤ w4[28]!*E*5*64^5 := by
  decide +kernel

end Borwein.BulkMomentChunk28
