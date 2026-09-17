import Borwein.LargeAnglePole

set_option autoImplicit false

namespace Borwein.ThreeFrequencyCusp
noncomputable section
open Complex Dilogarithm DilogarithmUpper ShiftedDilogarithm AngularKernel
  SmoothedResonantMain PositiveCuspCertificate

theorem basel_tail : (∑' j : ℕ, (1:ℝ)/((j+4:ℕ):ℝ)^2) = Real.pi^2/6-49/36 := by
  have h := hasSum_zeta_two.summable.sum_add_tsum_nat_add 4
  rw [hasSum_zeta_two.tsum_eq] at h
  norm_num [Finset.sum_range_succ] at h
  simp only [Nat.cast_add,Nat.cast_ofNat,one_div]
  linarith

theorem dilog_tail (w : ℂ) (hw : ‖w‖ ≤ 1) :
    ‖∑' j : ℕ, w^(j+4)/((j+4:ℕ):ℂ)^2‖ ≤ 13/45 := by
  have hs := ((summable_nat_add_iff 4).mpr hasSum_zeta_two.summable).hasSum
  rw [basel_tail] at hs
  have h : ‖∑' j : ℕ, w^(j+4)/((j+4:ℕ):ℂ)^2‖ ≤ Real.pi^2/6-49/36 := by
    apply tsum_of_norm_bounded hs
    intro j
    simp only [norm_div,norm_pow,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg w) hw) (sq_nonneg _)
  have hpi : Real.pi^2/6 ≤ (33/20:ℝ) := by nlinarith [Real.pi_lt_d4,Real.pi_pos]
  linarith

theorem minus_im_upper (w : ℂ) (hw : ‖w‖ ≤ 1) :
    -(dilog w).im ≤ -(w+w^2/4+w^3/9).im+13/45 := by
  have he := (summable_dilog w hw).sum_add_tsum_nat_add 4
  change _ = dilog w at he
  norm_num [Finset.sum_range_succ] at he
  have hi := congrArg Complex.im he
  simp only [Complex.add_im] at hi
  have ht := dilog_tail w hw
  have hr := Complex.im_le_norm (-(∑' j : ℕ, w^(j+4)/((j+4:ℕ):ℂ)^2))
  rw [Complex.neg_im,norm_neg] at hr
  simp only [Nat.cast_add,Nat.cast_ofNat] at ht hr
  simp only [Complex.add_im]
  linarith

theorem power_im (q t : ℝ) (k : ℕ) :
    ((((q:ℂ)*circle t)^k)/((k:ℂ)^2)).im = q^k*Real.sin ((k:ℝ)*t)/(k:ℝ)^2 := by
  rw [radial_pow,show (k:ℂ)^2 = (((k:ℝ)^2:ℝ):ℂ) by push_cast; rfl,Complex.div_ofReal_im]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  simp only [circle,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_add,add_zero]

theorem polar_upper (q t : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    -(dilog ((q:ℂ)*circle t)).im ≤
      -q*Real.sin t-q^2*Real.sin (2*t)/4-q^3*Real.sin (3*t)/9+13/45 := by
  have hw : ‖(q:ℂ)*circle t‖ ≤ 1 := by simpa [norm_mul,Real.norm_of_nonneg hq0,circle_norm] using hq1
  have h := minus_im_upper ((q:ℂ)*circle t) hw
  have h1 := power_im q t 1
  have h2 := power_im q t 2
  have h3 := power_im q t 3
  norm_num only [Nat.cast_one,pow_one,one_pow,mul_one,one_mul,div_one] at h1
  norm_num only [Nat.cast_ofNat] at h2 h3
  simp only [Complex.add_im] at h
  rw [h1,h2,h3] at h
  linarith

theorem coefficient_bound (a a0 s lo : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (haa : a0 ≤ a) (hlo : lo ≤ s) : -a*s ≤ max (-lo) (-a0*lo) := by
  have hm := mul_le_mul_of_nonneg_left hlo ha0
  by_cases hl : 0 ≤ lo
  · have h := mul_le_mul_of_nonneg_right haa hl
    exact (show -a*s ≤ -a0*lo by nlinarith).trans (le_max_right _ _)
  · have h := mul_le_mul_of_nonpos_right ha1 (le_of_not_ge hl)
    exact (show -a*s ≤ -lo by nlinarith).trans (le_max_left _ _)

theorem damping_bounds (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1/2) :
    (3/5:ℝ) ≤ Real.exp (-(PositiveCuspCertificate.eta+τ)) ∧ Real.exp (-(PositiveCuspCertificate.eta+τ)) ≤ 1 := by
  have hl : (3/5:ℝ) ≤ Real.exp (-(51/100:ℝ)) := by
    apply (ExpCertificate.exp_enclosure _ (3/5) 1 12 (by norm_num) (by norm_num) ?_ ?_).1
    all_goals norm_num [ExpCertificate.taylorSum,ExpCertificate.remainder,Finset.sum_range_succ,Nat.factorial]
  constructor
  · exact hl.trans (Real.exp_le_exp.mpr (by norm_num [PositiveCuspCertificate.eta]; linarith))
  · exact Real.exp_le_one_iff.mpr (by norm_num [PositiveCuspCertificate.eta]; linarith)

theorem pole_from_imaginary (η τ t M : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (ht : 0 < t) (hM : 0 ≤ M)
    (hi : -(dilog (Complex.exp (-((η:ℂ)+((τ:ℂ)-(t:ℂ)*I))))).im ≤ M*t) :
    poleIntegral 1 η ((τ:ℂ)-(t:ℂ)*I) ≤ M := by
  let W := dilog (Complex.exp (-((η:ℂ)+((τ:ℂ)-(t:ℂ)*I))))
  have hw : W.re ≤ radial η := by
    have h := norm_dilog_le ((η:ℂ)+((τ:ℂ)-(t:ℂ)*I)) (by simp; linarith)
    simp only [Complex.add_re,Complex.ofReal_re,Complex.sub_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,sub_self] at h
    exact (Complex.re_le_norm W).trans (h.trans (radial_mono hη.le (by linarith)))
  have hz0 : (τ:ℂ)-(t:ℂ)*I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  rw [pole_formula η _ hη (by simpa using hτ) hz0]
  change ((W-(radial η:ℂ))/((τ:ℂ)-(t:ℂ)*I)).re ≤ M
  simp only [Complex.div_re,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.normSq_apply,
    mul_zero,mul_one,add_zero,sub_zero,zero_sub]
  rw [← add_div]
  rw [show τ*τ+(-t)*(-t) = τ^2+t^2 by ring]
  apply (div_le_iff₀ (show 0 < τ^2+t^2 by positivity)).mpr
  have hr := mul_le_mul_of_nonneg_right hw hτ
  have hii := mul_le_mul_of_nonneg_right hi ht.le
  have hMτ : 0 ≤ M*τ^2 := by positivity
  change -W.im*t ≤ M*t*t at hii
  nlinarith

end
end Borwein.ThreeFrequencyCusp
