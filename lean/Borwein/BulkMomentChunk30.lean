import Borwein.BulkCandidateData

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Borwein.BulkMomentChunk30
open ComputedMomentTable BulkCandidateData

theorem variance_lower : v[30]!*E*3*64^3 ≤ S*lowerTotal 2 30 := by
  decide +kernel

theorem third_upper : S*upperTotal 3 30 ≤ w3[30]!*E*4*64^4 := by
  decide +kernel

theorem fourth_upper : S*upperTotal 4 30 ≤ w4[30]!*E*5*64^5 := by
  decide +kernel

end Borwein.BulkMomentChunk30
