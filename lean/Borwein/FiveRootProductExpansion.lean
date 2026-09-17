import Borwein.LogFactorProduct
import Borwein.ProductSmoothing

namespace Borwein.FiveRootProductExpansion
noncomputable section
open scoped BigOperators
open Set LogFactorDerivatives

def coefficients (ξ : ℂ) (j : Fin 4) : ℂ := ξ^(j.val+1)
def point (ξ z : ℂ) (n : ℕ) : ℂ := ξ*Complex.exp (-z/(5*n))

theorem factor_identity (ξ z : ℂ) (hξ : ξ^5 = 1) (n i : ℕ) (j : Fin 4) :
    (point ξ z n)^Borwein.exponent i j = w (coefficients ξ j) z (((i:ℝ)+shift j)/n) := by
  have hp : ξ^Borwein.exponent i j = ξ^(j.val+1) := by
    unfold Borwein.exponent
    rw [Nat.add_assoc,pow_add,pow_mul,hξ,one_pow,one_mul]
  unfold point w coefficients
  rw [mul_pow,hp,← Complex.exp_nat_mul]
  congr 1
  congr 1
  unfold Borwein.exponent shift
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem polynomial_as_product (ξ z : ℂ) (hξ : ξ^5 = 1) (n : ℕ) :
    Polynomial.eval₂ (Int.castRingHom ℂ) (point ξ z n) (Borwein.polynomial n) =
      ∏ j : Fin 4, ∏ k ∈ Finset.range n, kernel (coefficients ξ j) z (((k:ℝ)+shift j)/n) := by
  rw [← ProductSmoothing.value_eq_polynomial_eval]
  unfold ProductSmoothing.value
  simp_rw [factor_identity ξ z hξ]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  exact Fin.prod_univ_eq_prod_range (fun k => kernel (coefficients ξ j) z (((k:ℝ)+shift j)/n)) n

theorem polynomial_expansion (ξ z : ℂ) (hξ : ξ^5 = 1) (n : ℕ) (hn : 0 < n)
    (hk : ∀ j x, x ∈ Icc (0:ℝ) 1 → kernel (coefficients ξ j) z x ≠ 0) :
    Polynomial.eval₂ (Int.castRingHom ℂ) (point ξ z n) (Borwein.polynomial n) =
      Complex.exp (fourMain (coefficients ξ) z n+fourRemainder (coefficients ξ) z n) := by
  rw [polynomial_as_product ξ z hξ n]
  exact four_product_expansion _ _ n hn hk

theorem coefficients_norm (ξ : ℂ) (hξ : ‖ξ‖ ≤ 1) (j : Fin 4) : ‖coefficients ξ j‖ ≤ 1 := by
  unfold coefficients
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg ξ) hξ

theorem root_norm (ξ : ℂ) (hξ : ξ^5 = 1) : ‖ξ‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg ξ) (by decide : (5:ℕ) ≠ 0)).mp
  rw [← norm_pow,hξ,norm_one]

theorem small_box_norm (z : ℂ) (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 11/2) (hi : |z.im| ≤ 2/5) :
    ‖z‖ ≤ 28/5 := by
  have hr := pow_le_pow_left₀ hz0 hz1 2
  have him := pow_le_pow_left₀ (abs_nonneg z.im) hi 2
  have hs : ‖z‖^2 = z.re^2+z.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
  norm_num at hr him
  nlinarith [norm_nonneg z]

theorem polynomial_expansion_3400 (ξ z : ℂ) (hξ : ξ^5 = 1)
    (hz : 0 ≤ z.re) (hzmax : ‖z‖ ≤ 28/5)
    (hgap : ∀ j x, x ∈ Icc (0:ℝ) 1 → (3/4:ℝ) ≤ ‖kernel (coefficients ξ j) z x‖)
    (n : ℕ) (hn : 0 < n) :
    Polynomial.eval₂ (Int.castRingHom ℂ) (point ξ z n) (Borwein.polynomial n) =
      Complex.exp (fourMain (coefficients ξ) z n+fourRemainder (coefficients ξ) z n) ∧
      ‖fourRemainder (coefficients ξ) z n‖ ≤ 3400/(n:ℝ)^2 := by
  constructor
  · apply polynomial_expansion ξ z hξ n hn
    intro j
    exact uniform_kernel_ne_zero _ _ (3/4) (by norm_num) (hgap j)
  · exact four_remainder_3400 _ z (coefficients_norm ξ (root_norm ξ hξ).le) hz hzmax hgap n hn

end
end Borwein.FiveRootProductExpansion
