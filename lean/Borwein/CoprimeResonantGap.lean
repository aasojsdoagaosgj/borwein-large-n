import Borwein.UniformPoleBound
import Borwein.DivisibleResonantGap

set_option autoImplicit false

namespace Borwein.CoprimeResonantGap
noncomputable section
open DilogarithmUpper SmoothedResonantMain

theorem radial_two : radial 2 ≤ 4/25 := by
  have h1 : (8/3:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8/3) h1 2
  rw [← Real.exp_nat_mul] at h2
  norm_num at h2
  have he : Real.exp (-(2:ℝ)) ≤ 9/64 := by
    rw [Real.exp_neg,inv_eq_one_div]
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 64/9) h2
    norm_num at h
    simpa only [one_div] using h
  apply (DilogarithmTail.radial_upper 2 (9/64) (by norm_num) he (by norm_num)).trans
  apply (DilogarithmTail.series_upper 1 (9/64) (by norm_num) (by norm_num)).trans
  norm_num [Finset.sum_range_succ]

theorem scaled_half (b : ℕ) (η τ t : ℝ) (hb : 2 ≤ b) (hη : 0 < η) (hτ : 0 ≤ τ) :
    (4/(b:ℝ))*poleIntegral b η ((τ:ℂ)-(t:ℂ)*Complex.I) ≤ 1 := by
  have hb' : (2:ℝ) ≤ b := by exact_mod_cast hb
  rw [UniformPoleBound.pole_scale]
  have h := UniformPoleBound.half_upper (b*η) (b*τ) (b*t) (by positivity) (by positivity)
  have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 4/(b:ℝ))
  have hc : 4/(b:ℝ) ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  linarith

theorem scaled_radial (b : ℕ) (η τ t D : ℝ) (hb : 2 ≤ b) (hη : 0 < η) (hτ : 0 < τ)
    (hD : radial (b*τ) ≤ D) :
    (4/(b:ℝ))*poleIntegral b η ((τ:ℂ)-(t:ℂ)*Complex.I) ≤ D/τ := by
  have hb' : (2:ℝ) ≤ b := by exact_mod_cast hb
  have hD0 : 0 ≤ D := (radial_nonneg _).trans hD
  rw [UniformPoleBound.pole_scale]
  have h := UniformPoleBound.radial_upper (b*η) (b*τ) (b*t) (by positivity) (by positivity)
  have hd := div_le_div_of_nonneg_right hD (by positivity : 0 ≤ (b:ℝ)*τ)
  have hd' := div_le_div_of_nonneg_left hD0 (by positivity : (0:ℝ) < 2*τ)
    (show 2*τ ≤ (b:ℝ)*τ by nlinarith)
  have hp := h.trans (hd.trans hd')
  have hc : 4/(b:ℝ) ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4/(b:ℝ))
  have hm' := mul_le_mul_of_nonneg_right hc (div_nonneg hD0 (by positivity : 0 ≤ 2*τ))
  exact (hm.trans hm').trans_eq (by ring)

theorem uniform_gap (b : ℕ) (η τ t : ℝ) (hb : 2 ≤ b)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    (13/100:ℝ) ≤ PhaseIntegral.radialR τ-
      (4/(b:ℝ))*poleIntegral b η ((τ:ℂ)-(t:ℂ)*Complex.I) := by
  have hb' : (2:ℝ) ≤ b := by exact_mod_cast hb
  by_cases hs : τ ≤ 1/2
  · have hR := SmallRadialBaseline.small_radial_lower τ hs
    have hp := scaled_half b η τ t hb hη hτ
    linarith
  have hτpos : 0 < τ := by linarith
  have hR := (div_le_iff₀ hτpos).mp (PositiveRadialCusp.radial_lower τ hτpos)
  have hC := PositiveCuspCertificate.constants_lower.2
  by_cases hm : τ ≤ 1
  · have hB := (radial_mono (by norm_num : (0:ℝ) ≤ 1/2) (by linarith : 1/2 ≤ τ)).trans DilogarithmTail.radial_half
    have hB2 := (radial_mono (by norm_num : (0:ℝ) ≤ 1) (show 1 ≤ (b:ℝ)*τ by nlinarith)).trans DilogarithmTail.radial_one
    have hp := (le_div_iff₀ hτpos).mp (scaled_radial b η τ t (41/100) hb hη hτpos hB2)
    nlinarith
  · have hB := (radial_mono (by norm_num : (0:ℝ) ≤ 1) (by linarith : 1 ≤ τ)).trans DilogarithmTail.radial_one
    have hB2 := (radial_mono (by norm_num : (0:ℝ) ≤ 2) (show 2 ≤ (b:ℝ)*τ by nlinarith)).trans radial_two
    have hp := (le_div_iff₀ hτpos).mp (scaled_radial b η τ t (4/25) hb hη hτpos hB2)
    nlinarith

end
end Borwein.CoprimeResonantGap
