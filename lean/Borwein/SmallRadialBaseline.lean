import Borwein.PositiveCuspCertificate

set_option autoImplicit false

namespace Borwein.SmallRadialBaseline
noncomputable section
open PhaseIntegral PhaseGap PositiveRadialCusp DilogarithmUpper

theorem radialSum_antitone : Antitone radialSum := by
  intro u v huv
  unfold radialSum
  apply Finset.sum_le_sum
  intro j _
  apply Real.exp_le_exp.mpr
  have hj : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j.val
  nlinarith

theorem radialR_antitone : Antitone radialR := by
  intro u v huv
  unfold radialR
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_log_radialSum v).intervalIntegrable 0 1)
    ((continuous_log_radialSum u).intervalIntegrable 0 1)
  intro x hx
  apply Real.log_le_log (radialDenominator_pos _)
  exact radialSum_antitone (mul_le_mul_of_nonneg_right huv hx.1)

theorem small_radial_lower (τ : ℝ) (hτ : τ ≤ 1/2) : (144/125:ℝ) ≤ radialR τ := by
  apply le_trans _ (radialR_antitone hτ)
  have hR := PositiveRadialCusp.radial_lower (1/2) (by norm_num)
  have hC := PositiveCuspCertificate.constants_lower.2
  have hB := DilogarithmTail.radial_half
  norm_num at hR
  linarith

end
end Borwein.SmallRadialBaseline
