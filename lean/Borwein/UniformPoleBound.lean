import Borwein.CuspRectangleBridge

set_option autoImplicit false

namespace Borwein.UniformPoleBound
noncomputable section
open Complex Dilogarithm DilogarithmUpper ShiftedDilogarithm AngularKernel SmoothedResonantMain

theorem first_tail (w : ℂ) (hw : ‖w‖ ≤ 1) :
    ‖∑' j : ℕ, w^(j+2)/((j+2:ℕ):ℂ)^2‖ ≤ 13/20 := by
  have hb : (∑' j : ℕ, (1:ℝ)/((j+2:ℕ):ℝ)^2) = Real.pi^2/6-1 := by
    have h := hasSum_zeta_two.summable.sum_add_tsum_nat_add 2
    rw [hasSum_zeta_two.tsum_eq] at h
    norm_num [Finset.sum_range_succ] at h
    simp only [Nat.cast_add,Nat.cast_ofNat,one_div]
    linarith
  have hs := ((summable_nat_add_iff 2).mpr hasSum_zeta_two.summable).hasSum
  rw [hb] at hs
  have h : ‖∑' j : ℕ, w^(j+2)/((j+2:ℕ):ℂ)^2‖ ≤ Real.pi^2/6-1 := by
    apply tsum_of_norm_bounded hs
    intro j
    simp only [norm_div,norm_pow,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg w) hw) (sq_nonneg _)
  have hpi : Real.pi^2/6 ≤ (33/20:ℝ) := by nlinarith [Real.pi_lt_d4,Real.pi_pos]
  linarith

theorem first_imaginary (q t : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    -(dilog ((q:ℂ)*circle t)).im ≤ -q*Real.sin t+13/20 := by
  let w := (q:ℂ)*circle t
  have hw : ‖w‖ ≤ 1 := by simpa [w,norm_mul,Real.norm_of_nonneg hq0,circle_norm] using hq1
  have he := (summable_dilog w hw).sum_add_tsum_nat_add 2
  change _ = dilog w at he
  norm_num [Finset.sum_range_succ] at he
  have hi := congrArg Complex.im he
  simp only [Complex.add_im] at hi
  have ht := first_tail w hw
  have hr := Complex.im_le_norm (-(∑' j : ℕ, w^(j+2)/((j+2:ℕ):ℂ)^2))
  rw [Complex.neg_im,norm_neg] at hr
  simp only [Nat.cast_add,Nat.cast_ofNat] at ht hr
  have him : w.im = q*Real.sin t := by
    have h := ThreeFrequencyCusp.power_im q t 1
    norm_num only [Nat.cast_one,pow_one,one_pow,mul_one,one_mul,div_one] at h
    exact h
  change -(dilog w).im ≤ _
  rw [him] at hi
  linarith

theorem sine_compact (t : ℝ) (ht0 : 2 ≤ t) (ht1 : t ≤ 33/10) : -(3/10:ℝ) ≤ Real.sin t := by
  by_cases ht : t ≤ Real.pi
  · have hs := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ t) ht
    linarith
  · have h := Real.abs_sin_sub_sin_le t Real.pi
    rw [Real.sin_pi,sub_zero,abs_of_nonneg (by linarith : 0 ≤ t-Real.pi)] at h
    have hl := (abs_le.mp h).1
    linarith [Real.pi_gt_three]

theorem compact_upper (η τ t : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ)
    (ht0 : 2 ≤ t) (ht1 : t ≤ 33/10) : poleIntegral 1 η ((τ:ℂ)-(t:ℂ)*I) ≤ 1/2 := by
  have hq0 := (Real.exp_pos (-(η+τ))).le
  have hq1 : Real.exp (-(η+τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hs := sine_compact t ht0 ht1
  have hm := mul_le_mul_of_nonneg_left hs hq0
  have hi := first_imaginary (Real.exp (-(η+τ))) t hq0 hq1
  have he : Complex.exp (-((η:ℂ)+((τ:ℂ)-(t:ℂ)*I))) = (Real.exp (-(η+τ)):ℂ)*circle t := by
    rw [circle_eq_exp,Complex.ofReal_exp,← Complex.exp_add]
    congr 1
    push_cast
    ring
  apply ThreeFrequencyCusp.pole_from_imaginary η τ t (1/2) hη hτ (by linarith) (by norm_num)
  rw [he]
  nlinarith

theorem half_upper (η τ t : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) :
    poleIntegral 1 η ((τ:ℂ)-(t:ℂ)*I) ≤ 1/2 := by
  by_cases hs : |t| ≤ 2
  · linarith [SmallAngleIntegral.pole_small_angle η τ t hη hτ hs]
  by_cases hc : |t| ≤ 33/10
  · have h := compact_upper η τ |t| hη hτ (by linarith) hc
    rwa [CuspRectangleBridge.pole_abs] at h
  have hn : |t| ≤ ‖(τ:ℂ)-(t:ℂ)*I‖ := by
    simpa using Complex.abs_im_le_norm ((τ:ℂ)-(t:ℂ)*I)
  have hz : (τ:ℂ)-(t:ℂ)*I ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖(τ:ℂ)-(t:ℂ)*I‖)
  have h := pole_norm_upper η _ hη (by simpa using hτ) hz
  have hpi : Real.pi^2/6 ≤ (33/20:ℝ) := by nlinarith [Real.pi_lt_d4,Real.pi_pos]
  have hp : 0 < ‖(τ:ℂ)-(t:ℂ)*I‖ := norm_pos_iff.mpr hz
  apply h.trans
  apply (div_le_iff₀ hp).mpr
  linarith

theorem pole_scale (b : ℕ) (η τ t : ℝ) :
    poleIntegral b η ((τ:ℂ)-(t:ℂ)*I) =
      poleIntegral 1 (b*η) (((b*τ:ℝ):ℂ)-((b*t:ℝ):ℂ)*I) := by
  unfold poleIntegral
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  congr 3
  push_cast
  ring

theorem radial_upper (η τ t : ℝ) (hη : 0 < η) (hτ : 0 < τ) :
    poleIntegral 1 η ((τ:ℂ)-(t:ℂ)*I) ≤ radial τ/τ := by
  let z : ℂ := (τ:ℂ)-(t:ℂ)*I
  have hz : z.re = τ := by simp [z]
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz; linarith
  have hn : τ ≤ ‖z‖ := by simpa [hz] using Complex.re_le_norm z
  have hd := norm_dilog_le ((η:ℂ)+z) (by simp [hz]; linarith)
  simp only [Complex.add_re,Complex.ofReal_re,hz] at hd
  have hW := hd.trans (radial_mono hτ.le (by linarith))
  change poleIntegral 1 η z ≤ _
  rw [pole_formula η z hη (by simpa [hz] using hτ.le) hz0,sub_div,Complex.sub_re]
  have hR : 0 ≤ (((radial η:ℂ))/z).re := by
    simp only [Complex.div_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,add_zero,hz]
    exact div_nonneg (mul_nonneg (radial_nonneg η) hτ.le) (Complex.normSq_nonneg z)
  have h := Complex.re_le_norm (dilog (Complex.exp (-((η:ℂ)+z)))/z)
  rw [norm_div] at h
  have hb := div_le_div_of_nonneg_right hW (norm_nonneg z)
  have hb' := div_le_div_of_nonneg_left (radial_nonneg τ) hτ hn
  linarith

end
end Borwein.UniformPoleBound
