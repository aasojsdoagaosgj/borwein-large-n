import Borwein.BulkCandidateData

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Borwein.BulkMomentChunk12
open ComputedMomentTable BulkCandidateData

theorem variance_lower : v[12]!*E*3*64^3 ≤ S*lowerTotal 2 12 := by
  decide +kernel

theorem third_upper : S*upperTotal 3 12 ≤ w3[12]!*E*4*64^4 := by
  decide +kernel

theorem fourth_upper : S*upperTotal 4 12 ≤ w4[12]!*E*5*64^5 := by
  decide +kernel

end Borwein.BulkMomentChunk12
