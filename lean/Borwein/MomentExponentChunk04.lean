import Borwein.MomentExponentChainCertificate

namespace Borwein.MomentExponentChunk04
open MomentExponentData

theorem steps (j : Fin 256) :
    lo[1024+j.val+1]!*D ≤ lo[1024+j.val]!*stepLo ∧
      hi[1024+j.val]!*stepHi ≤ hi[1024+j.val+1]!*D := by
  exact MomentExponentChainCertificate.steps ⟨1024+j.val, by omega⟩

end Borwein.MomentExponentChunk04
