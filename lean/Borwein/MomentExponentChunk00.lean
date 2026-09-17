import Borwein.MomentExponentChainCertificate

namespace Borwein.MomentExponentChunk00
open MomentExponentData

theorem steps (j : Fin 256) :
    lo[0+j.val+1]!*D ≤ lo[0+j.val]!*stepLo ∧
      hi[0+j.val]!*stepHi ≤ hi[0+j.val+1]!*D := by
  exact MomentExponentChainCertificate.steps ⟨0+j.val, by omega⟩

end Borwein.MomentExponentChunk00
