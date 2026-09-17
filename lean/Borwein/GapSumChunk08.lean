import Borwein.GapSumData
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Borwein.GapSumChunk08
theorem checked : Borwein.GapSumData.block 8 = 595608686442557696469129584 := by decide
end Borwein.GapSumChunk08
