import Borwein.RoundedWeightData
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Borwein.RoundedWeightChunk12
theorem checked : ∀ d : Fin 4, ∀ j : Fin 25, Borwein.RoundedWeightData.Checks d (300+j.val) := by decide
end Borwein.RoundedWeightChunk12
