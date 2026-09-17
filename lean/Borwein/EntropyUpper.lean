import Borwein.PositiveRadialCusp
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

namespace Borwein.EntropyUpper
noncomputable section
open RadialSmoothingIncrement

theorem entropy_identity (c : ℝ) (hc : 0 < c) :
    entropy c = Real.log (1+c)+c*Real.log (1+1/c) := by
  rw [log_ratio 1 c (by norm_num) hc]
  simp only [add_comm c 1]
  unfold entropy
  ring

theorem entropy_upper (c L : ℝ) (hc : 0 < c) (hL : Real.log (1+1/c) ≤ L) :
    entropy c ≤ c*(1+L) := by
  rw [entropy_identity c hc]
  have hl := Real.log_le_sub_one_of_pos (show 0 < 1+c by linarith)
  have hm := mul_le_mul_of_nonneg_left hL hc.le
  nlinarith

theorem ratio_upper (η τ L : ℝ) (hη : 0 < η) (hτ : 0 < τ)
    (hL : 1+τ/η ≤ Real.exp L) : entropy (η/τ) ≤ (η/τ)*(1+L) := by
  apply entropy_upper _ L (div_pos hη hτ)
  rw [one_div_div]
  exact (Real.log_le_iff_le_exp (by positivity)).mpr hL

theorem exp_five_lower : (134:ℝ) ≤ Real.exp 5 := by
  have he : (8/3:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8/3) he 5
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  linarith

theorem exp_seven_lower : (950:ℝ) ≤ Real.exp 7 := by
  have he : (8/3:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8/3) he 7
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  linarith

end
end Borwein.EntropyUpper
