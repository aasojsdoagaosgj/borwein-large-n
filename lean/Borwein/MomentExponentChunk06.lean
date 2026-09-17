import Borwein.MomentExponentChainCertificate

namespace Borwein.MomentExponentChunk06
open MomentExponentData

theorem steps (j : Fin 256) :
    lo[1536+j.val+1]!*D ≤ lo[1536+j.val]!*stepLo ∧
      hi[1536+j.val]!*stepHi ≤ hi[1536+j.val+1]!*D := by
  exact MomentExponentChainCertificate.steps ⟨1536+j.val, by omega⟩

end Borwein.MomentExponentChunk06
