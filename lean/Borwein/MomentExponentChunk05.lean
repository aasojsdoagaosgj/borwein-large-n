import Borwein.MomentExponentChainCertificate

namespace Borwein.MomentExponentChunk05
open MomentExponentData

theorem steps (j : Fin 256) :
    lo[1280+j.val+1]!*D ≤ lo[1280+j.val]!*stepLo ∧
      hi[1280+j.val]!*stepHi ≤ hi[1280+j.val+1]!*D := by
  exact MomentExponentChainCertificate.steps ⟨1280+j.val, by omega⟩

end Borwein.MomentExponentChunk05
