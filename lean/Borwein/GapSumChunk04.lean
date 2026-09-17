import Borwein.GapSumData
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Borwein.GapSumChunk04
theorem checked : Borwein.GapSumData.block 4 = 631536604847626995826722432 := by decide
end Borwein.GapSumChunk04
