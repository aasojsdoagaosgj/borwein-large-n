import Borwein.MomentExponentChainCertificate

namespace Borwein.MomentExponentChunk03
open MomentExponentData

theorem steps (j : Fin 256) :
    lo[768+j.val+1]!*D ≤ lo[768+j.val]!*stepLo ∧
      hi[768+j.val]!*stepHi ≤ hi[768+j.val+1]!*D := by
  exact MomentExponentChainCertificate.steps ⟨768+j.val, by omega⟩

end Borwein.MomentExponentChunk03
