import Borwein.BulkCandidateData

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Borwein.BulkMomentChunk04
open ComputedMomentTable BulkCandidateData

theorem variance_lower : v[4]!*E*3*64^3 ≤ S*lowerTotal 2 4 := by
  decide +kernel

theorem third_upper : S*upperTotal 3 4 ≤ w3[4]!*E*4*64^4 := by
  decide +kernel

theorem fourth_upper : S*upperTotal 4 4 ≤ w4[4]!*E*5*64^5 := by
  decide +kernel

end Borwein.BulkMomentChunk04
