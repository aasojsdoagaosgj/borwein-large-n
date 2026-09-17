import Borwein.AmplitudeBounds
import Borwein.SecondOrderSegment

namespace Borwein.AmplitudeTaylor
noncomputable section
open scoped BigOperators
open Complex Set FiveRootProductExpansion MainTermIdentification AmplitudeDerivatives AmplitudeBounds ComplexMainIntegral

def a1 (τ : ℝ) : ℝ := (77/50)*firstBudget τ
def a2 (τ : ℝ) : ℝ := (77/100)*(secondBudget τ+(firstBudget τ)^2)

theorem logSecond_continuousOn (c : ℂ) (s : Set ℂ) (hk : ∀ z ∈ s, factor c z ≠ 0) :
    ContinuousOn (logSecond c) s := by
  unfold logSecond
  apply ContinuousOn.div
  · unfold radial; fun_prop
  · unfold factor radial; fun_prop
  · intro z hz
    exact pow_ne_zero 2 (hk z hz)

theorem amplitudeSecond_continuousOn (ξ : ℂ) (s : Set ℂ)
    (hs : ∀ z ∈ s, ∀ j, factor (coefficients ξ j) z ∈ Complex.slitPlane) :
    ContinuousOn (amplitudeSecond ξ) s := by
  have ha : ContinuousOn (amplitude ξ) s :=
    fun z hz => (amplitude_deriv ξ z (hs z hz)).continuousAt.continuousWithinAt
  have hl1 : ContinuousOn (lambdaFirst ξ) s :=
    fun z hz => (lambda_first_deriv ξ z (fun j => Complex.slitPlane_ne_zero (hs z hz j))).continuousAt.continuousWithinAt
  have hl2 : ContinuousOn (lambdaSecond ξ) s := by
    apply continuousOn_finsetSum
    intro j _
    exact (logSecond_continuousOn _ s (fun z hz => Complex.slitPlane_ne_zero (hs z hz j))).const_smul
      (PeanoQuadrature.B1 (LogFactorDerivatives.shift j))
  exact ha.mul (hl2.add (hl1.pow 2))

theorem amplitude_vertical_deriv (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun t => amplitude ξ (vertical z t))
      (((z.im:ℂ)*I)*amplitudeFirst ξ (vertical z t)) t := by
  have hb := vertical_box z hz hi t ht
  simpa only [Function.comp_def,smul_eq_mul] using
    ((small_box_derivatives ξ _ hξ hb.1 hb.2).2.2.1).scomp t (vertical_deriv z t)

theorem amplitude_vertical_second_deriv (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun t => ((z.im:ℂ)*I)*amplitudeFirst ξ (vertical z t))
      (((z.im:ℂ)*I)^2*amplitudeSecond ξ (vertical z t)) t := by
  have hb := vertical_box z hz hi t ht
  have h := (((small_box_derivatives ξ _ hξ hb.1 hb.2).2.2.2).scomp t (vertical_deriv z t)).const_mul ((z.im:ℂ)*I)
  convert! h using 1 <;> simp only [Function.comp_def,smul_eq_mul] <;> ring

theorem amplitude_vertical_second_continuous (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) :
    ContinuousOn (fun t => ((z.im:ℂ)*I)^2*amplitudeSecond ξ (vertical z t)) (Icc (0:ℝ) 1) := by
  have h := amplitudeSecond_continuousOn ξ {w | 0 ≤ w.re ∧ |w.im| ≤ 2/5}
    (fun w hw => AmplitudeDerivatives.coefficient_slit ξ w hξ hw.1 hw.2)
  exact (h.comp (by unfold vertical; fun_prop) (fun t ht => vertical_box z hz hi t ht)).const_mul _

theorem amplitude_variation (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) :
    ‖amplitude ξ z-amplitude ξ (z.re:ℂ)‖ ≤ a1 z.re*|z.im| := by
  have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) := amplitude_vertical_deriv ξ z hξ hz hi t ht
  have hb (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) :
      ‖((z.im:ℂ)*I)*amplitudeFirst ξ (vertical z t)‖ ≤ |z.im| * a1 z.re := by
    rw [norm_mul,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
    have hv := vertical_box z hz hi t ⟨ht.1,ht.2.le⟩
    have h := (amplitude_derivative_bounds ξ _ hξ hv.1 hv.2).1
    have hr : (vertical z t).re = z.re := by simp [vertical]
    rw [hr] at h
    exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hd t ht).hasDerivWithinAt) hb
  simpa only [vertical_one,vertical_zero,mul_comm] using h

theorem amplitude_quadratic_remainder (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) :
    ‖amplitude ξ z-amplitude ξ (z.re:ℂ)-((z.im:ℂ)*I)*amplitudeFirst ξ (z.re:ℂ)‖ ≤
      a2 z.re*z.im^2 := by
  have hb (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖((z.im:ℂ)*I)^2*amplitudeSecond ξ (vertical z t)‖ ≤
        z.im^2*((77/50)*(secondBudget z.re+(firstBudget z.re)^2)) := by
    rw [norm_mul,norm_pow,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    have hv := vertical_box z hz hi t ht
    have h := (amplitude_derivative_bounds ξ _ hξ hv.1 hv.2).2
    have hr : (vertical z t).re = z.re := by simp [vertical]
    rw [hr] at h
    exact mul_le_mul_of_nonneg_left h (sq_nonneg _)
  have h := SecondOrderSegment.remainder_bound
    (fun t => amplitude ξ (vertical z t))
    (fun t => ((z.im:ℂ)*I)*amplitudeFirst ξ (vertical z t))
    (fun t => ((z.im:ℂ)*I)^2*amplitudeSecond ξ (vertical z t))
    (z.im^2*((77/50)*(secondBudget z.re+(firstBudget z.re)^2)))
    (amplitude_vertical_deriv ξ z hξ hz hi) (amplitude_vertical_second_deriv ξ z hξ hz hi)
    (amplitude_vertical_second_continuous ξ z hξ hz hi) hb
  simp only [vertical_one,vertical_zero] at h
  convert h using 1 <;> unfold a2 <;> ring

theorem contour_variation (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (τ t : ℝ)
    (hτ : 0 ≤ τ) (ht : |t| ≤ 2/5) :
    ‖amplitude ξ ((τ:ℂ)-(t:ℂ)*I)-amplitude ξ (τ:ℂ)‖ ≤ a1 τ*|t| := by
  simpa using amplitude_variation ξ ((τ:ℂ)-(t:ℂ)*I) hξ (by simpa using hτ) (by simpa using ht)

theorem contour_quadratic_remainder (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (τ t : ℝ)
    (hτ : 0 ≤ τ) (ht : |t| ≤ 2/5) :
    ‖amplitude ξ ((τ:ℂ)-(t:ℂ)*I)-amplitude ξ (τ:ℂ)+(t:ℂ)*I*amplitudeFirst ξ (τ:ℂ)‖ ≤ a2 τ*t^2 := by
  have h := amplitude_quadratic_remainder ξ ((τ:ℂ)-(t:ℂ)*I) hξ (by simpa using hτ) (by simpa using ht)
  simpa using h

end
end Borwein.AmplitudeTaylor
