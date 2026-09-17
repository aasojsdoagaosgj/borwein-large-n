import Borwein.GapSumData
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Borwein.GapSumChunk05
theorem checked : Borwein.GapSumData.block 5 = 662992224942149861565766752 := by decide
end Borwein.GapSumChunk05
