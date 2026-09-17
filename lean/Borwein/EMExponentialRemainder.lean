import Borwein.FullGaussianReplacement

namespace Borwein.EMExponentialRemainder
noncomputable section
open scoped BigOperators
open Complex CombinedAmplitude MainTermIdentification FiveRootProductExpansion LogFactorDerivatives

def correctionBudget (z : ℂ) : ℝ := ‖z‖*((1/30:ℝ)+(8/75)*Real.exp (-z.re))
def exponentialBudget (d E n : ℝ) : ℝ := (E+d^2/2)/n^2*Real.exp (d/n+E/n^2)
def rootRemainder (ξ z : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (correction ξ z/(n:ℂ)+fourRemainder (coefficients ξ) z n)-1-correction ξ z/(n:ℂ)
def combinedRemainder (ζ : ℂ) (a n : ℕ) (z : ℂ) : ℂ :=
  ∑ j : Fin 4, phaseWeight ζ a j*amplitude (coefficients ζ j) z*rootRemainder (coefficients ζ j) z n

theorem correction_norm_bound (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5) (hi : |z.im| ≤ 2/5) :
    ‖correction ξ z‖ ≤ correctionBudget z := by
  rw [CorrectionCancellation.correction_decomposition ξ z hξ]
  have h1 : ‖-z/30‖ = ‖z‖/30 := by simp [norm_div]
  have h2 : ‖z*Complex.exp (-z)*CorrectionCancellation.residual ξ (Complex.exp (-z))‖ ≤
      ‖z‖*Real.exp (-z.re)*(8/75) := by
    rw [norm_mul,norm_mul,Complex.norm_exp,Complex.neg_re]
    exact mul_le_mul_of_nonneg_left (residual_bound ξ z hξ hi) (by positivity)
  have h := (norm_add_le _ _).trans (add_le_add (le_of_eq h1) h2)
  unfold correctionBudget
  convert! h using 1
  ring

theorem exponential_remainder_bound (D ε : ℂ) (d E n : ℝ) (hn : 0 < n)
    (hD : ‖D‖ ≤ d) (hε : ‖ε‖ ≤ E/n^2) :
    ‖Complex.exp (D/(n:ℂ)+ε)-1-D/(n:ℂ)‖ ≤ exponentialBudget d E n := by
  have hd0 := (norm_nonneg D).trans hD
  have he0 : 0 ≤ E/n^2 := (norm_nonneg ε).trans hε
  have hdn : ‖D/(n:ℂ)‖ ≤ d/n := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn]
    exact div_le_div_of_nonneg_right hD hn.le
  have hr : (D/(n:ℂ)).re ≤ d/n := (Complex.re_le_norm _).trans hdn
  have hrε : (D/(n:ℂ)+ε).re ≤ d/n+E/n^2 := by
    have h := (Complex.re_le_norm ε).trans hε
    simp only [Complex.add_re]
    linarith
  have ha := ExponentialSegment.difference_bound (D/(n:ℂ)+ε) (D/(n:ℂ))
    (d/n+E/n^2) hrε (by linarith)
  simp only [add_sub_cancel_left] at ha
  have ha' := ha.trans (mul_le_mul_of_nonneg_right hε (Real.exp_pos _).le)
  have hb := ExponentialSegment.quadratic_bound (D/(n:ℂ)) 0 (d/n+E/n^2)
    (by linarith) (by simp; positivity)
  simp only [sub_zero,Complex.exp_zero,mul_one] at hb
  have hb' := hb.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hdn 2) (by norm_num : (0:ℝ) ≤ 2))
    (Real.exp_pos _).le)
  have he : Complex.exp (D/(n:ℂ)+ε)-1-D/(n:ℂ) =
      (Complex.exp (D/(n:ℂ)+ε)-Complex.exp (D/(n:ℂ)))+
      (Complex.exp (D/(n:ℂ))-1-D/(n:ℂ)) := by ring
  rw [he]
  have h := (norm_add_le _ _).trans (add_le_add ha' hb')
  unfold exponentialBudget
  convert! h using 1
  ring

theorem root_remainder_bound (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5) (n : ℕ) (hn : 0 < n)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 11/2) (hi : |z.im| ≤ 2/5) :
    ‖rootRemainder ξ z n‖ ≤ exponentialBudget (correctionBudget z) 3400 n := by
  exact exponential_remainder_bound (correction ξ z) (fourRemainder (coefficients ξ) z n)
    (correctionBudget z) 3400 n (by exact_mod_cast hn) (correction_norm_bound ξ z hξ hi)
    (small_box_expansion ξ z hξ hz0 hz1 hi n hn).2

theorem combined_remainder_bound (ζ z : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a n : ℕ) (hn : 0 < n)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 11/2) (hi : |z.im| ≤ 2/5) :
    ‖combinedRemainder ζ a n z‖ ≤ (154/25:ℝ)*exponentialBudget (correctionBudget z) 3400 n := by
  have h := weighted_sum_bound ζ hζ a
    (fun j => amplitude (coefficients ζ j) z*rootRemainder (coefficients ζ j) z n)
    ((77/50)*exponentialBudget (correctionBudget z) 3400 n) (by
      intro j
      rw [norm_mul]
      exact mul_le_mul (AmplitudeBounds.amplitude_norm_bound _ z (coefficient_primitive ζ hζ j) hz0 hi)
        (root_remainder_bound _ z (coefficient_primitive ζ hζ j) n hn hz0 hz1 hi)
        (norm_nonneg _) (by norm_num))
  simp only [combinedRemainder,mul_assoc] at h ⊢
  convert! h using 1
  ring

theorem four_root_decomposition (ζ z : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a n : ℕ) (hn : 0 < n)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 11/2) (hi : |z.im| ≤ 2/5) :
    (∑ j : Fin 4, phaseWeight ζ a j*
      Polynomial.eval₂ (Int.castRingHom ℂ) (point (coefficients ζ j) z n) (Borwein.polynomial n)) =
      Complex.exp ((n:ℂ)*PhaseIntegral.complexR z)*
        (psi ζ a z+theta ζ a z/(n:ℂ)+combinedRemainder ζ a n z) := by
  rw [four_root_polynomial_expansion ζ z hζ a n hn hz0 hz1 hi]
  congr 1
  unfold psi theta combinedRemainder rootRemainder
  rw [Finset.sum_div,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end Borwein.EMExponentialRemainder
