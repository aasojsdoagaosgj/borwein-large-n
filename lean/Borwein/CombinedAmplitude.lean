import Borwein.AmplitudeTaylor
import Borwein.CorrectionCancellation

namespace Borwein.CombinedAmplitude
noncomputable section
open scoped BigOperators
open Complex FiveRootProductExpansion MainTermIdentification AmplitudeDerivatives AmplitudeTaylor

def phaseWeight (ζ : ℂ) (a : ℕ) (j : Fin 4) : ℂ := (coefficients ζ j)^(-(a:ℤ))
def psi (ζ : ℂ) (a : ℕ) (z : ℂ) : ℂ := ∑ j : Fin 4, phaseWeight ζ a j*amplitude (coefficients ζ j) z
def psiFirst (ζ : ℂ) (a : ℕ) (z : ℂ) : ℂ := ∑ j : Fin 4, phaseWeight ζ a j*amplitudeFirst (coefficients ζ j) z
def theta (ζ : ℂ) (a : ℕ) (z : ℂ) : ℂ := ∑ j : Fin 4,
  phaseWeight ζ a j*amplitude (coefficients ζ j) z*correction (coefficients ζ j) z
def correctionProfile (ζ : ℂ) (a : ℕ) (z : ℂ) : ℂ := ∑ j : Fin 4,
  phaseWeight ζ a j*amplitude (coefficients ζ j) z*
    CorrectionCancellation.residual (coefficients ζ j) (Complex.exp (-z))

theorem coefficient_primitive (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (j : Fin 4) :
    IsPrimitiveRoot (coefficients ζ j) 5 := by
  apply hζ.pow_of_coprime
  have hj := j.isLt
  interval_cases j.val <;> norm_num

theorem phaseWeight_norm (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (j : Fin 4) :
    ‖phaseWeight ζ a j‖ = 1 := by
  have hn : ‖coefficients ζ j‖ = 1 := by simp [coefficients,norm_pow,root_norm ζ hζ.pow_eq_one]
  simp [phaseWeight,norm_zpow,hn]

theorem weighted_sum_bound (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ)
    (f : Fin 4 → ℂ) (B : ℝ) (hf : ∀ j, ‖f j‖ ≤ B) :
    ‖∑ j : Fin 4, phaseWeight ζ a j*f j‖ ≤ 4*B := by
  have h : ‖∑ j : Fin 4, phaseWeight ζ a j*f j‖ ≤ ∑ _j : Fin 4, B := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    simpa only [norm_mul,phaseWeight_norm ζ hζ a j,one_mul] using hf j
  simpa using h

theorem psi_deriv (ζ z : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) : HasDerivAt (psi ζ a) (psiFirst ζ a z) z := by
  apply HasDerivAt.fun_sum
  intro j _
  exact ((small_box_derivatives _ z (coefficient_primitive ζ hζ j) hz hi).2.2.1).const_mul _

theorem psi_contour_variation (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ)
    (τ t : ℝ) (hτ : 0 ≤ τ) (ht : |t| ≤ 2/5) :
    ‖psi ζ a ((τ:ℂ)-(t:ℂ)*I)-psi ζ a (τ:ℂ)‖ ≤ 4*a1 τ*|t| := by
  have h := weighted_sum_bound ζ hζ a
    (fun j => amplitude (coefficients ζ j) ((τ:ℂ)-(t:ℂ)*I)-amplitude (coefficients ζ j) (τ:ℂ))
    (a1 τ*|t|) (fun j => contour_variation _ (coefficient_primitive ζ hζ j) τ t hτ ht)
  simpa only [mul_sub,Finset.sum_sub_distrib,psi,mul_assoc] using h

theorem psi_contour_quadratic (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ)
    (τ t : ℝ) (hτ : 0 ≤ τ) (ht : |t| ≤ 2/5) :
    ‖psi ζ a ((τ:ℂ)-(t:ℂ)*I)-psi ζ a (τ:ℂ)+(t:ℂ)*I*psiFirst ζ a (τ:ℂ)‖ ≤ 4*a2 τ*t^2 := by
  have h := weighted_sum_bound ζ hζ a
    (fun j => amplitude (coefficients ζ j) ((τ:ℂ)-(t:ℂ)*I)-amplitude (coefficients ζ j) (τ:ℂ)+
      (t:ℂ)*I*amplitudeFirst (coefficients ζ j) (τ:ℂ))
    (a2 τ*t^2) (fun j => contour_quadratic_remainder _ (coefficient_primitive ζ hζ j) τ t hτ ht)
  have he : (∑ j : Fin 4, phaseWeight ζ a j*
      (amplitude (coefficients ζ j) ((τ:ℂ)-(t:ℂ)*I)-amplitude (coefficients ζ j) (τ:ℂ)+
      (t:ℂ)*I*amplitudeFirst (coefficients ζ j) (τ:ℂ))) =
      psi ζ a ((τ:ℂ)-(t:ℂ)*I)-psi ζ a (τ:ℂ)+(t:ℂ)*I*psiFirst ζ a (τ:ℂ) := by
    unfold psi psiFirst
    rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at h
  simpa only [mul_assoc] using h

theorem theta_decomposition (ζ z : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) :
    theta ζ a z = -z/30*psi ζ a z+z*Complex.exp (-z)*correctionProfile ζ a z := by
  unfold theta psi correctionProfile
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [CorrectionCancellation.correction_decomposition _ z (coefficient_primitive ζ hζ j)]
  ring

theorem residual_bound (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5) (hi : |z.im| ≤ 2/5) :
    ‖CorrectionCancellation.residual ξ (Complex.exp (-z))‖ ≤ 8/75 := by
  have hb : (∑ j : Fin 4, |PeanoQuadrature.B2 (LogFactorDerivatives.shift j)|) = (4/25:ℝ) := by
    norm_num [Fin.sum_univ_four,LogFactorDerivatives.shift,PeanoQuadrature.B2]
  have hn (j : Fin 4) : ‖coefficients ξ j‖ = 1 := by simp [coefficients,norm_pow,root_norm ξ hξ.pow_eq_one]
  have hg (j : Fin 4) : (3/4:ℝ) ≤ ‖1-coefficients ξ j*Complex.exp (-z)‖ := by
    simpa [LogFactorDerivatives.kernel,LogFactorDerivatives.w] using
      FifthRootSeparation.coefficient_gap ξ z hξ hi j 1 (by norm_num)
  have hs : ‖∑ j : Fin 4, (PeanoQuadrature.B2 (LogFactorDerivatives.shift j):ℂ)*coefficients ξ j/
      (1-coefficients ξ j*Complex.exp (-z))‖ ≤ (4/25)/(3/4) := by
    calc
      _ ≤ ∑ j : Fin 4, ‖(PeanoQuadrature.B2 (LogFactorDerivatives.shift j):ℂ)*coefficients ξ j/
          (1-coefficients ξ j*Complex.exp (-z))‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin 4, |PeanoQuadrature.B2 (LogFactorDerivatives.shift j)|/(3/4) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,hn,mul_one]
        exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (hg j)
      _ = _ := by rw [← Finset.sum_div,hb]
  unfold CorrectionCancellation.residual
  rw [norm_mul]
  norm_num only [norm_div,norm_one,Complex.norm_ofNat]
  nlinarith

theorem correctionProfile_bound (ζ z : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) : ‖correctionProfile ζ a z‖ ≤ 1232/1875 := by
  have h := weighted_sum_bound ζ hζ a
    (fun j => amplitude (coefficients ζ j) z*CorrectionCancellation.residual (coefficients ζ j) (Complex.exp (-z)))
    ((77/50)*(8/75)) (by
      intro j
      rw [norm_mul]
      exact mul_le_mul (AmplitudeBounds.amplitude_norm_bound _ z (coefficient_primitive ζ hζ j) hz hi)
        (residual_bound _ z (coefficient_primitive ζ hζ j) hi) (norm_nonneg _) (by norm_num))
  norm_num at h
  simpa only [correctionProfile,mul_assoc] using h

theorem theta_small_factor (ζ z : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) :
    ‖theta ζ a z+z/30*psi ζ a z‖ ≤ (1232/1875)*‖z‖*Real.exp (-z.re) := by
  have he : theta ζ a z+z/30*psi ζ a z = z*Complex.exp (-z)*correctionProfile ζ a z := by
    rw [theta_decomposition ζ z hζ a]
    ring
  rw [he,norm_mul,norm_mul,Complex.norm_exp,Complex.neg_re]
  have h := mul_le_mul_of_nonneg_left (correctionProfile_bound ζ z hζ a hz hi)
    (mul_nonneg (norm_nonneg z) (Real.exp_pos (-z.re)).le)
  simpa only [mul_assoc,mul_comm,mul_left_comm] using h

theorem four_root_polynomial_expansion (ζ z : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a n : ℕ)
    (hn : 0 < n) (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 11/2) (hi : |z.im| ≤ 2/5) :
    (∑ j : Fin 4, phaseWeight ζ a j*
      Polynomial.eval₂ (Int.castRingHom ℂ) (point (coefficients ζ j) z n) (Borwein.polynomial n)) =
    Complex.exp ((n:ℂ)*PhaseIntegral.complexR z)*
      ∑ j : Fin 4, phaseWeight ζ a j*amplitude (coefficients ζ j) z*
        Complex.exp (correction (coefficients ζ j) z/(n:ℂ)+
          LogFactorDerivatives.fourRemainder (coefficients (coefficients ζ j)) z n) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [(MainTermIdentification.small_box_expansion _ z (coefficient_primitive ζ hζ j) hz0 hz1 hi n hn).1]
  ring

end
end Borwein.CombinedAmplitude
