import Borwein.MomentExponentChainCertificate

namespace Borwein.MomentExponentChunk01
open MomentExponentData

theorem steps (j : Fin 256) :
    lo[256+j.val+1]!*D ≤ lo[256+j.val]!*stepLo ∧
      hi[256+j.val]!*stepHi ≤ hi[256+j.val+1]!*D := by
  exact MomentExponentChainCertificate.steps ⟨256+j.val, by omega⟩

end Borwein.MomentExponentChunk01
