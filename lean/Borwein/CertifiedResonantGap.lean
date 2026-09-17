import Borwein.GapSumBridge
import Borwein.GapSumChunk00
import Borwein.GapSumChunk01
import Borwein.GapSumChunk02
import Borwein.GapSumChunk03
import Borwein.GapSumChunk04
import Borwein.GapSumChunk05
import Borwein.GapSumChunk06
import Borwein.GapSumChunk07
import Borwein.GapSumChunk08
import Borwein.GapSumChunk09
import Borwein.GapSumChunk10
import Borwein.GapSumChunk11
import Borwein.GapSumChunk12
import Borwein.GapSumChunk13
import Borwein.GapSumChunk14
import Borwein.GapSumChunk15

namespace Borwein.CertifiedResonantGap
noncomputable section
open Borwein.GapSumData Borwein.GapSumBridge

theorem total_value : total = 7620198428065017423779902464 := by
  rw [total_eq_blocks]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Borwein.GapSumChunk00.checked,
    Borwein.GapSumChunk01.checked,
    Borwein.GapSumChunk02.checked,
    Borwein.GapSumChunk03.checked,
    Borwein.GapSumChunk04.checked,
    Borwein.GapSumChunk05.checked,
    Borwein.GapSumChunk06.checked,
    Borwein.GapSumChunk07.checked,
    Borwein.GapSumChunk08.checked,
    Borwein.GapSumChunk09.checked,
    Borwein.GapSumChunk10.checked,
    Borwein.GapSumChunk11.checked,
    Borwein.GapSumChunk12.checked,
    Borwein.GapSumChunk13.checked,
    Borwein.GapSumChunk14.checked,
    Borwein.GapSumChunk15.checked]
  norm_num

theorem lowerGap_exact : Borwein.CheckedWeights.lowerGap =
    (2480533342469081192636687:ℝ)/250000000000000000000000000 := by
  rw [lowerGap_eq_total, total_value]
  norm_num [denominator]

theorem lowerGap_gt : (31:ℝ)/3125 < Borwein.CheckedWeights.lowerGap := by
  rw [lowerGap_exact]
  norm_num

theorem uniformGap_gt : (31:ℝ)/3125 <
    Borwein.SmoothedCertificate.uniformGap (113/40000) (11/2) (6/5) 400 :=
  lt_of_lt_of_le lowerGap_gt Borwein.CheckedWeights.lowerGap_le

theorem smoothed_modulus_gap (τ t : ℝ) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) (ht : 6/5 ≤ |t|) :
    Borwein.SmoothedPhase.smoothedModulus (113/40000) τ t <
      Borwein.PhaseIntegral.radialR τ-(31:ℝ)/3125 := by
  have h := Borwein.CheckedWeights.modulus_upper τ t hτ hT ht
  have hg := lowerGap_gt
  linarith

end
end Borwein.CertifiedResonantGap

