import Borwein.GapSumData
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Borwein.GapSumChunk02
theorem checked : Borwein.GapSumData.block 2 = 313703232447148794040735008 := by decide
end Borwein.GapSumChunk02
