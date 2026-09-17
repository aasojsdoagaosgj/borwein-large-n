import Borwein.BulkCandidateData

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Borwein.BulkMomentChunk16
open ComputedMomentTable BulkCandidateData

theorem variance_lower : v[16]!*E*3*64^3 ≤ S*lowerTotal 2 16 := by
  decide +kernel

theorem third_upper : S*upperTotal 3 16 ≤ w3[16]!*E*4*64^4 := by
  decide +kernel

theorem fourth_upper : S*upperTotal 4 16 ≤ w4[16]!*E*5*64^5 := by
  decide +kernel

end Borwein.BulkMomentChunk16
