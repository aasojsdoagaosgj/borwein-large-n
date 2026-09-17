import Borwein.RoundedWeightData
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Borwein.RoundedWeightChunk07
theorem checked : ∀ d : Fin 4, ∀ j : Fin 25, Borwein.RoundedWeightData.Checks d (175+j.val) := by decide
end Borwein.RoundedWeightChunk07
