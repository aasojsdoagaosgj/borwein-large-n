import Borwein.AmplitudeDerivatives
import Mathlib.Analysis.Complex.Exponential

namespace Borwein.AmplitudeBounds
noncomputable section
open scoped BigOperators
open Complex Set FiveRootProductExpansion MainTermIdentification AmplitudeDerivatives ComplexMainIntegral

def firstBudget (τ : ℝ) : ℝ := (16/15)*Real.exp (-τ)
def secondBudget (τ : ℝ) : ℝ := (64/45)*Real.exp (-τ)

theorem firstBudget_nonneg (τ : ℝ) : 0 ≤ firstBudget τ := by unfold firstBudget; positivity
theorem secondBudget_nonneg (τ : ℝ) : 0 ≤ secondBudget τ := by unfold secondBudget; positivity

theorem bernoulli_abs_sum :
    (∑ j : Fin 4, |PeanoQuadrature.B1 (LogFactorDerivatives.shift j)|) = (4/5:ℝ) := by
  norm_num [Fin.sum_univ_four,LogFactorDerivatives.shift,PeanoQuadrature.B1]

theorem weighted_norm_bound (f : Fin 4 → ℂ) (B : ℝ) (hf : ∀ j, ‖f j‖ ≤ B) :
    ‖∑ j : Fin 4, PeanoQuadrature.B1 (LogFactorDerivatives.shift j) • f j‖ ≤ (4/5)*B := by
  calc
    _ ≤ ∑ j : Fin 4, ‖PeanoQuadrature.B1 (LogFactorDerivatives.shift j) • f j‖ := norm_sum_le _ _
    _ = ∑ j : Fin 4, |PeanoQuadrature.B1 (LogFactorDerivatives.shift j)| * ‖f j‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ∑ j : Fin 4, |PeanoQuadrature.B1 (LogFactorDerivatives.shift j)| * B := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hf j) (abs_nonneg _)
    _ = (4/5)*B := by rw [← Finset.sum_mul,bernoulli_abs_sum]

theorem coefficient_radial_norm (ξ z : ℂ) (hξ : ξ^5 = 1) (j : Fin 4) :
    ‖radial (coefficients ξ j) z‖ = Real.exp (-z.re) := by
  simp [radial,coefficients,norm_mul,norm_pow,root_norm ξ hξ,Complex.norm_exp]

theorem logarithmic_bounds (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5) (hi : |z.im| ≤ 2/5) :
    ‖lambdaFirst ξ z‖ ≤ firstBudget z.re ∧ ‖lambdaSecond ξ z‖ ≤ secondBudget z.re := by
  have hg (j : Fin 4) : (3/4:ℝ) ≤ ‖factor (coefficients ξ j) z‖ := by
    rw [factor_eq_kernel]
    exact FifthRootSeparation.coefficient_gap ξ z hξ hi j 1 (by norm_num)
  constructor
  · have h := weighted_norm_bound (fun j => logFirst (coefficients ξ j) z) (Real.exp (-z.re)/(3/4)) (by
      intro j
      rw [logFirst,norm_div,coefficient_radial_norm ξ z hξ.pow_eq_one]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) (hg j))
    convert h using 1 <;> simp only [lambdaFirst,firstBudget] <;> ring
  · have h := weighted_norm_bound (fun j => logSecond (coefficients ξ j) z) (Real.exp (-z.re)/(3/4)^2) (by
      intro j
      rw [logSecond,norm_div,norm_neg,norm_pow,coefficient_radial_norm ξ z hξ.pow_eq_one]
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num)
      exact pow_le_pow_left₀ (by norm_num) (hg j) 2)
    convert h using 1 <;> simp only [lambdaSecond,secondBudget] <;> ring

theorem vertical_deriv (z : ℂ) (t : ℝ) : HasDerivAt (vertical z) ((z.im:ℂ)*I) t := by
  have hi : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 t := by
    convert! Complex.ofRealCLM.hasDerivAt (x := t) using 1
  unfold vertical
  convert! ((hi.mul_const (z.im:ℂ)).mul_const I).const_add (z.re:ℂ) using 1 <;> ring

theorem lambda_vertical_deriv (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun t => lambda ξ (vertical z t))
      (((z.im:ℂ)*I)*lambdaFirst ξ (vertical z t)) t := by
  have hb := vertical_box z hz hi t ht
  simpa only [Function.comp_def,smul_eq_mul] using
    ((small_box_derivatives ξ _ hξ hb.1 hb.2).1).scomp t (vertical_deriv z t)

theorem lambda_vertical_bound (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) :
    ‖lambda ξ z-lambda ξ (z.re:ℂ)‖ ≤ |z.im| * firstBudget z.re := by
  have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) := lambda_vertical_deriv ξ z hξ hz hi t ht
  have hb (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) :
      ‖((z.im:ℂ)*I)*lambdaFirst ξ (vertical z t)‖ ≤ |z.im| * firstBudget z.re := by
    rw [norm_mul,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
    have hv := vertical_box z hz hi t ⟨ht.1,ht.2.le⟩
    have h := (logarithmic_bounds ξ _ hξ hv.2).1
    have hr : (vertical z t).re = z.re := by simp [vertical]
    rw [hr] at h
    exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hd t ht).hasDerivWithinAt) hb
  simpa only [vertical_one,vertical_zero] using h

theorem amplitude_norm_local (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) :
    ‖amplitude ξ z‖ ≤ Real.exp (|z.im| * firstBudget z.re) := by
  rw [amplitude,Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h := (Complex.re_le_norm (lambda ξ z-lambda ξ (z.re:ℂ))).trans
    (lambda_vertical_bound ξ z hξ hz hi)
  simpa only [Complex.sub_re,lambda_real_re ξ hξ z.re hz,sub_zero] using h

theorem exp_amplitude_budget : Real.exp (32/75:ℝ) < 77/50 := by
  have h := Real.exp_bound (x := (32/75:ℝ)) (by norm_num : |(32/75:ℝ)| ≤ 1) (by norm_num : 0 < (10:ℕ))
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have h' := (abs_le.mp h).2
  linarith

theorem amplitude_norm_bound (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) : ‖amplitude ξ z‖ ≤ 77/50 := by
  apply (amplitude_norm_local ξ z hξ hz hi).trans
  apply le_trans _ exp_amplitude_budget.le
  apply Real.exp_le_exp.mpr
  have he : Real.exp (-z.re) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)
  have h1 : firstBudget z.re ≤ 16/15 := by unfold firstBudget; nlinarith
  have h := mul_le_mul hi h1 (firstBudget_nonneg z.re) (by norm_num : (0:ℝ) ≤ 2/5)
  norm_num at h
  exact h

theorem amplitude_derivative_bounds (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) :
    ‖amplitudeFirst ξ z‖ ≤ (77/50)*firstBudget z.re ∧
    ‖amplitudeSecond ξ z‖ ≤ (77/50)*(secondBudget z.re+(firstBudget z.re)^2) := by
  have hl := logarithmic_bounds ξ z hξ hi
  have ha := amplitude_norm_bound ξ z hξ hz hi
  constructor
  · rw [amplitudeFirst,norm_mul]
    exact mul_le_mul ha hl.1 (norm_nonneg _) (by norm_num)
  · rw [amplitudeSecond,norm_mul]
    apply mul_le_mul ha _ (norm_nonneg _) (by norm_num)
    have h := norm_add_le (lambdaSecond ξ z) ((lambdaFirst ξ z)^2)
    rw [norm_pow] at h
    exact h.trans (add_le_add hl.2 (pow_le_pow_left₀ (norm_nonneg _) hl.1 2))

end
end Borwein.AmplitudeBounds
