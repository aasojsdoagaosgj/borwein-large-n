import Borwein.CuspSineData

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Borwein.CuspSineChunk4
open CuspCellCertificate CuspSineData

theorem valid : ∀ i : Fin 160, i.val / 20 = 4 → Valid i.val (row i) := by
  decide +kernel

end Borwein.CuspSineChunk4
