import Borwein.EndpointWeakTail

set_option autoImplicit false

namespace Borwein.EndpointWeakPolynomial
noncomputable section
open Complex FivePoleCircle EndpointRootAsymptotic EndpointRootCancellation EndpointWeakTail

def character (a : ℕ) (j : Fin 4) : ℂ := zeta^(-((a*(j.val+1):ℕ):ℤ))
def polynomialDifference (a n : ℕ) (w : ℂ) : ℂ := ∑ j : Fin 4, character a j*
  (Polynomial.eval₂ (Int.castRingHom ℂ) (zeta^(j.val+1)*exp (-w)) (Borwein.polynomial n)-
    EndpointEta.G (zeta^(j.val+1)*exp (-w)))
def etaRemainder (a n : ℕ) (w : ℂ) : ℂ := ∑ j : Fin 4, character a j*
  (EndpointEta.G (zeta^(j.val+1)*exp (-w))-kappa j*main w)*
    (EndpointFiniteConnection.tail n (zeta^(j.val+1)*exp (-w))-1)

/-- The eta error keeps T_n-1; it is not replaced by an error for G alone. -/
theorem polynomial_decomposition (a n : ℕ) (w : ℂ) (hw : 0 < w.re) :
    polynomialDifference a n w=filteredMain a n w+etaRemainder a n w := by
  unfold polynomialDifference filteredMain filtered etaRemainder
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [EndpointFiniteConnection.polynomial_eq_G_tail n _ (EndpointFiniteConnection.root_norm j w hw)]
  unfold character weight
  ring

theorem character_norm (a : ℕ) (j : Fin 4) : ‖character a j‖=1 := by
  have hz := FiveRootProductExpansion.root_norm zeta zeta_primitive.pow_eq_one
  simp only [character, norm_zpow, hz, one_zpow]

theorem etaRemainder_factored (a n : ℕ) (w : ℂ) (hw : 0 < w.re) :
    etaRemainder a n w = ∑ j : Fin 4, weight a j*main w*(correction j w-1)*
      (EndpointFiniteConnection.tail n (zeta^(j.val+1)*exp (-w))-1) := by
  unfold etaRemainder
  apply Finset.sum_congr rfl
  intro j _
  rw [four_root_expansion j w hw]
  unfold character weight
  ring

/-- A tail-factor bound remains an explicit input until the all-angle tail estimate is proved. -/
theorem etaRemainder_bound (a n : ℕ) (v y B : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000)
    (hy : |y| ≤ 3*v/4) (hB : 0 ≤ B)
    (hT : ∀ j : Fin 4, ‖EndpointFiniteConnection.tail n
      (zeta^(j.val+1)*exp (-((v:ℂ)+(y:ℂ)*I)))-1‖ ≤ B) :
    ‖etaRemainder a n ((v:ℂ)+(y:ℂ)*I)‖ ≤ 40*‖main ((v:ℂ)+(y:ℂ)*I)‖*Real.exp (-1/v)*B := by
  rw [etaRemainder_factored a n _ (by simpa using hv)]
  apply (norm_sum_le _ _).trans
  have hb : ∑ j : Fin 4, ‖weight a j*main ((v:ℂ)+(y:ℂ)*I)*(correction j ((v:ℂ)+(y:ℂ)*I)-1)*
      (EndpointFiniteConnection.tail n (zeta^(j.val+1)*exp (-((v:ℂ)+(y:ℂ)*I)))-1)‖ ≤
      ∑ _j : Fin 4, ‖main ((v:ℂ)+(y:ℂ)*I)‖*(10*Real.exp (-1/v))*B := by
    apply Finset.sum_le_sum
    intro j _
    simp only [norm_mul, EndpointRootLinear.weight_norm, one_mul]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (correction_error j v y hv hV hy) (norm_nonneg _))
      (hT j) (norm_nonneg _) (by positivity)
  exact hb.trans_eq (by simp; ring)

end
end Borwein.EndpointWeakPolynomial
