import Borwein.GapSumData
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Borwein.GapSumChunk10
theorem checked : Borwein.GapSumData.block 10 = 504459623871140021095204656 := by decide
end Borwein.GapSumChunk10
