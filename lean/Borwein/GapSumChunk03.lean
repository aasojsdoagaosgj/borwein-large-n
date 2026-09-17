import Borwein.GapSumData
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Borwein.GapSumChunk03
theorem checked : Borwein.GapSumData.block 3 = 508482232907701002264539424 := by decide
end Borwein.GapSumChunk03
