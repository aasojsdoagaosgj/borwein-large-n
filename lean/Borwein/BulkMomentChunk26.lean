import Borwein.BulkCandidateData

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Borwein.BulkMomentChunk26
open ComputedMomentTable BulkCandidateData

theorem variance_lower : v[26]!*E*3*64^3 ≤ S*lowerTotal 2 26 := by
  decide +kernel

theorem third_upper : S*upperTotal 3 26 ≤ w3[26]!*E*4*64^4 := by
  decide +kernel

theorem fourth_upper : S*upperTotal 4 26 ≤ w4[26]!*E*5*64^5 := by
  decide +kernel

end Borwein.BulkMomentChunk26
