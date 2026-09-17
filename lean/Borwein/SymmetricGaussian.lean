import Borwein.GaussianMoments
import Borwein.CombinedAmplitude

namespace Borwein.SymmetricGaussian
noncomputable section
open Complex Set MeasureTheory GaussianMoments CombinedAmplitude AmplitudeTaylor

theorem odd_integral (f : ℝ → ℂ) (h : ℝ) (hf : ∀ t, f (-t) = -f t) :
    (∫ t in -h..h, f t) = 0 := by
  have he := intervalIntegral.integral_comp_neg (f := f) (a := -h) (b := h)
  simp only [hf,neg_neg,intervalIntegral.integral_neg] at he
  linear_combination (-1/2:ℂ)*he

theorem odd_gaussian_integral (C1 C3 : ℂ) (c h : ℝ) :
    (∫ t in -h..h, (C1*(t:ℂ)+C3*(t:ℂ)^3)*(gaussian c t:ℂ)) = 0 := by
  apply odd_integral
  intro t
  rw [gaussian_even,Complex.ofReal_neg]
  ring

theorem linear_gaussian_integral (C : ℂ) (c h : ℝ) :
    (∫ t in -h..h, C*(t:ℂ)*(gaussian c t:ℂ)) = 0 := by
  simpa using odd_gaussian_integral C 0 c h

theorem weighted_remainder_bound (r : ℝ → ℂ) (c h K : ℝ) (k : ℕ) (hh : 0 ≤ h)
    (hr : ContinuousOn r (Icc (-h) h))
    (hb : ∀ t ∈ Icc (-h) h, ‖r t‖ ≤ K*t^(2*k)) :
    ‖∫ t in -h..h, r t*(gaussian c t:ℂ)‖ ≤ K*moment c h k := by
  have hg : Continuous (gaussian c) := by unfold gaussian; fun_prop
  have hi : ContinuousOn (fun t => r t*(gaussian c t:ℂ)) (Icc (-h) h) :=
    hr.mul (Complex.continuous_ofReal.comp hg).continuousOn
  calc
    _ ≤ ∫ t in -h..h, ‖r t*(gaussian c t:ℂ)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith : -h ≤ h)
    _ ≤ ∫ t in -h..h, K*t^(2*k)*gaussian c t := by
      apply intervalIntegral.integral_mono_on (by linarith : -h ≤ h)
        (hi.norm.intervalIntegrable_of_Icc (by linarith))
        ((by fun_prop : Continuous (fun t : ℝ => K*t^(2*k)*gaussian c t)).intervalIntegrable (-h) h)
      intro t ht
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (gaussian_nonneg c t)]
      exact mul_le_mul_of_nonneg_right (hb t ht) (gaussian_nonneg c t)
    _ = K*moment c h k := by rw [moment]; simp only [mul_assoc,intervalIntegral.integral_const_mul]

theorem linear_subtraction (A : ℝ → ℂ) (A0 A1 : ℂ) (c h : ℝ) (hh : 0 ≤ h)
    (hA : ContinuousOn A (Icc (-h) h)) :
    (∫ t in -h..h, A t*(gaussian c t:ℂ))-A0*(∫ t in -h..h, (gaussian c t:ℂ)) =
    ∫ t in -h..h, (A t-A0-A1*(t:ℂ))*(gaussian c t:ℂ) := by
  have hg : Continuous (fun t : ℝ => (gaussian c t:ℂ)) := by unfold gaussian; fun_prop
  have hiA : IntervalIntegrable (fun t => A t*(gaussian c t:ℂ)) volume (-h) h :=
    (hA.mul hg.continuousOn).intervalIntegrable_of_Icc (by linarith : -h ≤ h)
  have hi0 : IntervalIntegrable (fun t : ℝ => A0*(gaussian c t:ℂ)) volume (-h) h :=
    (continuous_const.mul hg).intervalIntegrable _ _
  have hi1 : IntervalIntegrable (fun t : ℝ => A1*(t:ℂ)*(gaussian c t:ℂ)) volume (-h) h :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub (hiA.sub hi0) hi1,
    intervalIntegral.integral_sub hiA hi0,linear_gaussian_integral,sub_zero,
    intervalIntegral.integral_const_mul]

theorem amplitude_replacement (A : ℝ → ℂ) (A0 A1 : ℂ) (c h K : ℝ)
    (hc : 0 < c) (hh : 0 ≤ h) (hK : 0 ≤ K) (hA : ContinuousOn A (Icc (-h) h))
    (hb : ∀ t ∈ Icc (-h) h, ‖A t-A0-A1*(t:ℂ)‖ ≤ K*t^2) :
    ‖(∫ t in -h..h, A t*(gaussian c t:ℂ))-A0*(∫ t in -h..h, (gaussian c t:ℂ))‖ ≤
      K*Real.sqrt (Real.pi/c)/(2*c) := by
  rw [linear_subtraction A A0 A1 c h hh hA]
  have hr : ContinuousOn (fun t : ℝ => A t-A0-A1*(t:ℂ)) (Icc (-h) h) :=
    (hA.sub continuousOn_const).sub (by fun_prop)
  have hbnd := weighted_remainder_bound _ c h K 1 hh hr (by simpa using hb)
  have hm := mul_le_mul_of_nonneg_left (moment_two_le c h hc hh) hK
  exact hbnd.trans (by simpa only [mul_div_assoc] using hm)

theorem psi_continuousOn_contour (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ)
    (τ h : ℝ) (hτ : 0 ≤ τ) (hh : h ≤ 2/5) :
    ContinuousOn (fun t : ℝ => psi ζ a ((τ:ℂ)-(t:ℂ)*I)) (Icc (-h) h) := by
  intro t ht
  have ht' : |t| ≤ 2/5 := (abs_le.mpr ht).trans hh
  have hd := psi_deriv ζ ((τ:ℂ)-(t:ℂ)*I) hζ a (by simpa using hτ) (by simpa using ht')
  have hpath : Continuous (fun t : ℝ => (τ:ℂ)-(t:ℂ)*I) := by fun_prop
  exact hd.continuousAt.comp_continuousWithinAt
    (f := fun s : ℝ => (τ:ℂ)-(s:ℂ)*I) (x := t) hpath.continuousWithinAt

theorem psi_gaussian_replacement (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ)
    (τ c h : ℝ) (hτ : 0 ≤ τ) (hc : 0 < c) (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) :
    ‖(∫ t in -h..h, psi ζ a ((τ:ℂ)-(t:ℂ)*I)*(gaussian c t:ℂ))-
      psi ζ a (τ:ℂ)*(∫ t in -h..h, (gaussian c t:ℂ))‖ ≤
      4*a2 τ*Real.sqrt (Real.pi/c)/(2*c) := by
  apply amplitude_replacement _ _ (-I*psiFirst ζ a (τ:ℂ)) c h (4*a2 τ) hc hh0
  · unfold a2 AmplitudeBounds.secondBudget
    positivity
  · exact psi_continuousOn_contour ζ hζ a τ h hτ hh1
  · intro t ht
    have ht' : |t| ≤ 2/5 := (abs_le.mpr ht).trans hh1
    have he : psi ζ a ((τ:ℂ)-(t:ℂ)*I)-psi ζ a (τ:ℂ)-(-I*psiFirst ζ a (τ:ℂ))*(t:ℂ) =
        psi ζ a ((τ:ℂ)-(t:ℂ)*I)-psi ζ a (τ:ℂ)+(t:ℂ)*I*psiFirst ζ a (τ:ℂ) := by ring
    rw [he]
    exact psi_contour_quadratic ζ hζ a τ t hτ ht'

end
end Borwein.SymmetricGaussian
