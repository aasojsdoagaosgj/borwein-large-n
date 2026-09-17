import Borwein.MomentExponentChainCertificate

namespace Borwein.MomentExponentChunk07
open MomentExponentData

theorem steps (j : Fin 256) :
    lo[1792+j.val+1]!*D ≤ lo[1792+j.val]!*stepLo ∧
      hi[1792+j.val]!*stepHi ≤ hi[1792+j.val+1]!*D := by
  exact MomentExponentChainCertificate.steps ⟨1792+j.val, by omega⟩

end Borwein.MomentExponentChunk07
