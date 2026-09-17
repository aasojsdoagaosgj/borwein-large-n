import Borwein.RogersProductFinite
import Borwein.EulerPentagonalLimit

set_option autoImplicit false

namespace Borwein.RogersProductLimit
noncomputable section
open Complex EndpointEta EulerQBinomial EulerGaussianLimit EulerFiniteBinomial
  RogersThetaExponent RogersProductFinite Filter
open scoped Topology

def infiniteProduct (Q z : ℂ) : ℂ := ∏' j : ℕ, (1+z*Q^j)

theorem product_multipliable (Q z : ℂ) (hQ : ‖Q‖ < 1) :
    Multipliable (fun j : ℕ => 1+z*Q^j) := by
  apply multipliable_one_add_of_summable
  simpa only [norm_mul, Complex.norm_pow] using
    (summable_geometric_of_lt_one (norm_nonneg Q) hQ).mul_left ‖z‖

theorem product_limit (Q z : ℂ) (hQ : ‖Q‖ < 1) :
    Tendsto (fun n : ℕ => product Q z n) atTop (𝓝 (infiniteProduct Q z)) :=
  (product_multipliable Q z hQ).tendsto_prod_tprod_nat

theorem centered_limit (q : ℂ) (hq : ‖q‖ < 1) (a : ℕ) (j : ℤ) :
    Tendsto (fun n : ℕ => centered q a n j) atTop
      (𝓝 ((euler (q^5))⁻¹*thetaTerm q a j)) := by
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have hh := (EulerPentagonalLimit.shifted_gaussian_limit (q^5) j hq5).mul_const (thetaTerm q a j)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop j.natAbs] with n hn
  have habs : -(j.natAbs:ℤ) ≤ j := by
    rw [Int.natCast_natAbs]
    exact neg_abs_le j
  rw [centered, IntegerQBinomial.choose, if_pos (by omega)]

theorem centered_bound (q : ℂ) (hq0 : q ≠ 0) (a : ℕ) (ha : a ≤ 1)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ n k : ℕ, ‖gaussian (q^5) n k‖ ≤ M)
    (n : ℕ) (j : ℤ) : ‖centered q a n j‖ ≤ M*‖q‖^(degree a j) := by
  rw [centered, norm_mul, term_norm q hq0 a ha j]
  exact mul_le_mul_of_nonneg_right (RogersGaussianLimit.integer_bound (q^5) M hM hb _ _) (by positivity)

theorem centered_sum_limit (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (a : ℕ) (ha : a ≤ 1) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, centered q a n j) atTop
      (𝓝 ((euler (q^5))⁻¹*(∑' j : ℤ, thetaTerm q a j))) := by
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  obtain ⟨M,hM,hb⟩ := gaussian_bounded (q^5) hq5
  have hh := tendsto_tsum_of_dominated_convergence
    ((majorant_summable q hq a ha).mul_left M)
    (fun j => centered_limit q hq a j)
    (Eventually.of_forall (fun n j => centered_bound q hq0 a ha M hM.le hb n j))
  simpa only [tsum_mul_left] using hh

/-- Jacobi's product specialized to the two theta series required here. -/
theorem theta_product (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (a : ℕ) (ha : a ≤ 1) :
    (∑' j : ℤ, thetaTerm q a j)=euler (q^5)*
      (infiniteProduct (q^5) (-q^(offset a))*infiniteProduct (q^5) (-(q^5)/q^(offset a))) := by
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have hl := (product_limit (q^5) (-q^(offset a)) hq5).mul
    (product_limit (q^5) (-(q^5)/q^(offset a)) hq5)
  have he : (fun n : ℕ => product (q^5) (-q^(offset a)) n*
      product (q^5) (-(q^5)/q^(offset a)) n)=
      (fun n : ℕ => ∑' j : ℤ, centered q a n j) :=
    funext (fun n => finite_product_sum q hq hq0 a n ha)
  rw [he] at hl
  have hh := tendsto_nhds_unique hl (centered_sum_limit q hq hq0 a ha)
  rw [hh, ← mul_assoc, mul_inv_cancel₀ (euler_ne_zero (q^5) hq5), one_mul]

theorem series_product_ratio (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (a : ℕ) (ha : a ≤ 1) :
    (∑' k : ℕ, RogersSeriesLimit.seriesTerm q a k)=(euler q)⁻¹*euler (q^5)*
      (infiniteProduct (q^5) (-q^(offset a))*infiniteProduct (q^5) (-(q^5)/q^(offset a))) := by
  rw [RogersSeriesLimit.analytic_identity q hq hq0 a ha, theta_product q hq hq0 a ha]
  ring

end
end Borwein.RogersProductLimit
