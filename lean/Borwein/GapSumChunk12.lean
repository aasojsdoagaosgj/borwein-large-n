import Borwein.GapSumData
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Borwein.GapSumChunk12
theorem checked : Borwein.GapSumData.block 12 = 403346647670282687299183808 := by decide
end Borwein.GapSumChunk12
