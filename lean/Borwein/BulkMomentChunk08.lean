import Borwein.BulkCandidateData

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Borwein.BulkMomentChunk08
open ComputedMomentTable BulkCandidateData

theorem variance_lower : v[8]!*E*3*64^3 ≤ S*lowerTotal 2 8 := by
  decide +kernel

theorem third_upper : S*upperTotal 3 8 ≤ w3[8]!*E*4*64^4 := by
  decide +kernel

theorem fourth_upper : S*upperTotal 4 8 ≤ w4[8]!*E*5*64^5 := by
  decide +kernel

end Borwein.BulkMomentChunk08
