import Borwein.BulkCandidateData

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Borwein.BulkMomentChunk00
open ComputedMomentTable BulkCandidateData

theorem variance_lower : v[0]!*E*3*64^3 ≤ S*lowerTotal 2 0 := by
  decide +kernel

theorem third_upper : S*upperTotal 3 0 ≤ w3[0]!*E*4*64^4 := by
  decide +kernel

theorem fourth_upper : S*upperTotal 4 0 ≤ w4[0]!*E*5*64^5 := by
  decide +kernel

end Borwein.BulkMomentChunk00
