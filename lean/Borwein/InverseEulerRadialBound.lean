import Borwein.EndpointEtaBounds

set_option autoImplicit false

namespace Borwein.InverseEulerRadialBound
noncomputable section
open Complex EndpointEta EndpointPositiveCusp EndpointEtaBounds

theorem radial_identity (u : ℝ) (hu : 0 < u) :
    euler (Real.exp (-u):ℂ) = (Real.sqrt (2*Real.pi/u):ℂ)*
      (Real.exp (u/24-Real.pi^2/(6*u)):ℂ)*euler (Real.exp (-4*Real.pi^2/u):ℂ) := by
  let z : ℂ := ((2*Real.pi/u:ℝ):ℂ)*I
  have hz : 0 < z.im := by dsimp [z]; simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re]; positivity
  have hq0 : q (-1/z) = (Real.exp (-u):ℂ) := by
    rw [Complex.ofReal_exp]
    unfold q
    congr 1
    dsimp [z]
    push_cast
    field_simp
    <;> ring_nf
    <;> simp [I_sq]
  have hq1 : q z = (Real.exp (-4*Real.pi^2/u):ℂ) := by
    rw [Complex.ofReal_exp]
    unfold q
    congr 1
    dsimp [z]
    push_cast
    ring_nf
    simp [I_sq]
  have hex : (Real.pi:ℂ)*I*(z+1/z)/12 = ((u/24-Real.pi^2/(6*u):ℝ):ℂ) := by
    dsimp [z]
    push_cast
    field_simp
    <;> ring_nf
    <;> simp [I_sq]
  have hs : sqrt z = (Real.sqrt (2*Real.pi/u):ℂ)*sqrt I :=
    sqrt_scale _ I (by positivity) I_ne_zero
  have hIs : sqrt I ≠ 0 := by rw [sqrt_eq_exp I_ne_zero]; exact exp_ne_zero _
  have he := euler_inversion z hz
  rw [hq0, hq1, hex, ← Complex.ofReal_exp, hs] at he
  have hc : (sqrt I)⁻¹*((Real.sqrt (2*Real.pi/u):ℂ)*sqrt I) =
      (Real.sqrt (2*Real.pi/u):ℂ) := by field_simp
  rwa [hc] at he

theorem transformed_small (u : ℝ) (hu : 0 < u) (hU : u ≤ 13/2000) :
    Real.exp (-4*Real.pi^2/u) ≤ 1/10 := by
  have ht : (10:ℝ) ≤ 4*Real.pi^2/u := by
    apply (le_div_iff₀ hu).mpr
    nlinarith [Real.pi_gt_d2]
  have he : (10:ℝ) ≤ Real.exp (4*Real.pi^2/u) := by
    linarith [Real.add_one_le_exp (4*Real.pi^2/u)]
  rw [show -4*Real.pi^2/u = -(4*Real.pi^2/u) by ring, Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<10) he

theorem transformed_lower (u : ℝ) (hu : 0 < u) (hU : u ≤ 13/2000) :
    (1/2:ℝ) ≤ ‖euler (Real.exp (-4*Real.pi^2/u):ℂ)‖ := by
  have hb := euler_error_small (Real.exp (-4*Real.pi^2/u):ℂ) (1/10) (by norm_num)
    (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact transformed_small u hu hU)
  have ht := norm_sub_norm_le (1:ℂ) (euler (Real.exp (-4*Real.pi^2/u):ℂ))
  rw [norm_one, norm_sub_rev] at ht
  linarith

theorem inverse_radial (u : ℝ) (hu : 0 < u) (hU : u ≤ 13/2000) :
    ‖(euler (Real.exp (-u):ℂ))⁻¹‖ ≤
      Real.sqrt u*Real.exp (Real.pi^2/(6*u)) := by
  have hs := Real.sqrt_pos.mpr hu
  have hp : 0 < Real.sqrt (2*Real.pi/u) := by positivity
  have hsmall := transformed_lower u hu hU
  have hn := congrArg norm (radial_identity u hu)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (Real.exp_pos _)] at hn
  have hden : 0 < ‖euler (Real.exp (-4*Real.pi^2/u):ℂ)‖ := by linarith
  rw [norm_inv, hn, mul_inv_rev, mul_inv_rev]
  have hi : ‖euler (Real.exp (-4*Real.pi^2/u):ℂ)‖⁻¹ ≤ 2 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2) hsmall
  have he : (Real.exp (u/24-Real.pi^2/(6*u)))⁻¹ ≤ Real.exp (Real.pi^2/(6*u)) := by
    rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    linarith
  have htwo : 2*(Real.sqrt (2*Real.pi/u))⁻¹ ≤ Real.sqrt u := by
    rw [Real.sqrt_div (by positivity), inv_div]
    have hpi : 2 ≤ Real.sqrt (2*Real.pi) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity), Real.sqrt_nonneg (2*Real.pi), Real.pi_gt_d2]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < Real.sqrt (2*Real.pi) by positivity)).mpr
    nlinarith
  rw [← mul_assoc]
  calc
    _ ≤ 2*Real.exp (Real.pi^2/(6*u))*(Real.sqrt (2*Real.pi/u))⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul hi he (by positivity) (by norm_num)) (by positivity)
    _ = (2*(Real.sqrt (2*Real.pi/u))⁻¹)*Real.exp (Real.pi^2/(6*u)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le

end
end Borwein.InverseEulerRadialBound
