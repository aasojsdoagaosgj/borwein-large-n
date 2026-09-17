import Borwein.PhaseAngleRange

set_option autoImplicit false

namespace Borwein.ElementaryPhaseConstants
noncomputable section
open PhaseAngleRange

theorem cosine_first : (4/5:ℝ) ≤ Real.cos (Real.pi/5) ∧ Real.cos (Real.pi/5) ≤ 81/100 := by
  rw [Real.cos_pi_div_five]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg (5:ℝ)
  constructor <;> nlinarith

theorem cosine_second : (3/10:ℝ) ≤ Real.cos (2*Real.pi/5) ∧ Real.cos (2*Real.pi/5) ≤ 31/100 := by
  have hroot := Real.quadratic_root_cos_pi_div_five
  have hd := Real.cos_two_mul (Real.pi/5)
  have he : 2*(Real.pi/5) = 2*Real.pi/5 := by ring
  rw [he] at hd
  constructor <;> nlinarith [cosine_first.1,cosine_first.2]

theorem cot_second : (3/10:ℝ) ≤ c2 ∧ c2 ≤ 1/3 := by
  have hp := Real.pi_pos
  have hs := Real.sin_pos_of_pos_of_lt_pi (by positivity : (0:ℝ) < 2*Real.pi/5) (by linarith)
  have hc := cosine_second
  have hunit := Real.sin_sq_add_cos_sq (2*Real.pi/5)
  have hslo : (94/100:ℝ) ≤ Real.sin (2*Real.pi/5) := by nlinarith
  unfold c2
  constructor
  · apply (le_div_iff₀ hs).mpr
    nlinarith [Real.sin_le_one (2*Real.pi/5)]
  · apply (div_le_iff₀ hs).mpr
    linarith

theorem first_slope (v : ℝ) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    (47/100:ℝ) ≤ c1/(1+(v*c1)^2) := by
  have hc := c1_bounds
  have hvc : 0 ≤ v*c1 := mul_nonneg hv.1 (by linarith)
  have hvc1 : v*c1 ≤ c1 := by nlinarith [hv.2]
  have hsq := pow_le_pow_left₀ hvc hvc1 2
  have hprod := mul_nonneg (show 0 ≤ c1-1 by linarith) (show 0 ≤ 7/5-c1 by linarith)
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 1+(v*c1)^2)).mpr
  nlinarith

theorem second_slope (v : ℝ) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    (27/100:ℝ) ≤ c2/(1+(v*c2)^2) ∧ c2/(1+(v*c2)^2) ≤ 1/3 := by
  have hc := cot_second
  have hvc : 0 ≤ v*c2 := mul_nonneg hv.1 (by linarith)
  have hvc1 : v*c2 ≤ (1/3:ℝ) := by nlinarith [hv.2]
  have hsq := pow_le_pow_left₀ hvc hvc1 2
  have hd : (0:ℝ) < 1+(v*c2)^2 := by positivity
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (v*c2)]

theorem angle_slopes (v : ℝ) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    (1/5:ℝ) ≤ (c1/(1+(v*c1)^2)+2*c2/(1+(v*c2)^2))/5 ∧
    (3/25:ℝ) ≤ (2*c1/(1+(v*c1)^2)-c2/(1+(v*c2)^2))/5 := by
  have h1 := first_slope v hv
  have h2 := second_slope v hv
  simp only [mul_div_assoc]
  constructor <;> linarith [h2.1,h2.2]

end
end Borwein.ElementaryPhaseConstants
