import Borwein.BulkCandidateData

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Borwein.BulkMomentChunk09
open ComputedMomentTable BulkCandidateData

theorem variance_lower : v[9]!*E*3*64^3 ≤ S*lowerTotal 2 9 := by
  decide +kernel

theorem third_upper : S*upperTotal 3 9 ≤ w3[9]!*E*4*64^4 := by
  decide +kernel

theorem fourth_upper : S*upperTotal 4 9 ≤ w4[9]!*E*5*64^5 := by
  decide +kernel

end Borwein.BulkMomentChunk09
