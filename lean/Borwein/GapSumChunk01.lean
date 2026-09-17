import Borwein.GapSumData
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Borwein.GapSumChunk01
theorem checked : Borwein.GapSumData.block 1 = 97340270434954502068425024 := by decide
end Borwein.GapSumChunk01
