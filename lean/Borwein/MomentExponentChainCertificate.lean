import Borwein.MomentExponentData

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Borwein.MomentExponentChainCertificate
open MomentExponentData

-- Each array is checked in one traversal, avoiding repeated kernel index reduction.
private theorem lower_chain :
    List.IsChain (fun a b : Nat => b*D ≤ a*stepLo) lo.toList := by
  decide +kernel

private theorem upper_chain :
    List.IsChain (fun a b : Nat => a*stepHi ≤ b*D) hi.toList := by
  decide +kernel

theorem steps (j : Fin 2048) :
    lo[j.val+1]!*D ≤ lo[j.val]!*stepLo ∧
      hi[j.val]!*stepHi ≤ hi[j.val+1]!*D := by
  have hl1 : j.val+1 < lo.size := by rw [sizes.1]; omega
  have hl0 : j.val < lo.size := by omega
  have hu1 : j.val+1 < hi.size := by rw [sizes.2]; omega
  have hu0 : j.val < hi.size := by omega
  have hl := lower_chain.getElem j.val (by simpa using hl1)
  have hu := upper_chain.getElem j.val (by simpa using hu1)
  constructor
  · simpa only [Array.getElem_toList, getElem!_pos lo j.val hl0,
      getElem!_pos lo (j.val+1) hl1] using hl
  · simpa only [Array.getElem_toList, getElem!_pos hi j.val hu0,
      getElem!_pos hi (j.val+1) hu1] using hu

end Borwein.MomentExponentChainCertificate
