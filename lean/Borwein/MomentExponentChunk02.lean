import Borwein.MomentExponentChainCertificate

namespace Borwein.MomentExponentChunk02
open MomentExponentData

theorem steps (j : Fin 256) :
    lo[512+j.val+1]!*D ≤ lo[512+j.val]!*stepLo ∧
      hi[512+j.val]!*stepHi ≤ hi[512+j.val+1]!*D := by
  exact MomentExponentChainCertificate.steps ⟨512+j.val, by omega⟩

end Borwein.MomentExponentChunk02
