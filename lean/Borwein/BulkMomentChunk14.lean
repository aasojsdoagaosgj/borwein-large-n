import Borwein.BulkCandidateData

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Borwein.BulkMomentChunk14
open ComputedMomentTable BulkCandidateData

theorem variance_lower : v[14]!*E*3*64^3 ≤ S*lowerTotal 2 14 := by
  decide +kernel

theorem third_upper : S*upperTotal 3 14 ≤ w3[14]!*E*4*64^4 := by
  decide +kernel

theorem fourth_upper : S*upperTotal 4 14 ≤ w4[14]!*E*5*64^5 := by
  decide +kernel

end Borwein.BulkMomentChunk14
