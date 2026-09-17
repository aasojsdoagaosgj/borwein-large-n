import Borwein.PentagonalOuterSum
import Borwein.FifthRootMiddle

set_option autoImplicit false

namespace Borwein.FifthRootOuter
noncomputable section
open Complex PowerSeries FivePoleCircle EndpointEta EulerWeakFilter EulerPentagonalCenter
  EulerPentagonalLimit FormalSeriesValue FormalSeriesOperations RogersProducts

def first (q : ℂ) : ℂ := ((residue (q^5) 1*residue (q^5) 4)⁻¹)^2
def second (q : ℂ) : ℂ := q^2*((residue (q^5) 2*residue (q^5) 3)⁻¹)^2
def firstSeries : ℤ⟦X⟧ := PowerSeries.expand 5 (by omega) ((rrSeries 1)^2)
def secondSeries : ℤ⟦X⟧ := PowerSeries.X^2*PowerSeries.expand 5 (by omega) ((rrSeries 2)^2)

theorem atom_filter (q : ℂ) (a : ℕ) (ha : a < 5) (k : ℤ) :
    (∑ j : Fin 5, zeta^(-((a*j.val:ℕ):ℤ))*atom (zeta^j.val*q) k)=
      5*PentagonalOuterSum.filtered q a k := by
  have he (j : Fin 5) : zeta^(-((a*j.val:ℕ):ℤ))*atom (zeta^j.val*q) k=
      (zeta^(-((a*j.val:ℕ):ℤ))*(zeta^j.val)^(pentagonal k))*atom q k := by
    simp only [atom, mul_pow]
    ring
  simp_rw [he]
  rw [← Finset.sum_mul, FifthRootMiddle.monomial_filter, Nat.mod_eq_of_lt ha]
  unfold PentagonalOuterSum.filtered
  split_ifs <;> ring

theorem euler_filter (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (a : ℕ) (ha : a < 5) :
    (∑ j : Fin 5, zeta^(-((a*j.val:ℕ):ℤ))*euler (zeta^j.val*q))=
      5*(∑' k : ℤ, PentagonalOuterSum.filtered q a k) := by
  have hqj (j : Fin 5) : ‖zeta^j.val*q‖ < 1 := by rw [rotated_norm]; exact hq
  have hs (j : Fin 5) : Summable (fun k : ℤ => zeta^(-((a*j.val:ℕ):ℤ))*atom (zeta^j.val*q) k) :=
    (atom_summable _ (hqj j)).mul_left _
  simp_rw [euler_pentagonal_nonzero _ (hqj _) (mul_ne_zero (pow_ne_zero _ zeta_nonzero) hq0),
    ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun j _ => hs j)]
  simp_rw [atom_filter q a ha]

theorem G_filter (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (a : ℕ) (ha : a < 5) :
    (∑ j : Fin 5, zeta^(-((a*j.val:ℕ):ℤ))*G (zeta^j.val*q))=
      5*(∑' k : ℤ, PentagonalOuterSum.filtered q a k)/euler (q^5) := by
  have he (j : Fin 5) : (zeta^j.val*q)^5=q^5 := by
    have hp : (zeta^j.val)^5=(zeta^5)^j.val := by
      simp only [← pow_mul]
      rw [Nat.mul_comm]
    rw [mul_pow, hp, zeta_primitive.pow_eq_one, one_pow, one_mul]
  simp_rw [G, he, ← mul_div_assoc]
  rw [← Finset.sum_div, euler_filter q hq hq0 a ha]

theorem G_first_filter (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    (∑ j : Fin 5, zeta^(-((0*j.val:ℕ):ℤ))*G (zeta^j.val*q))=5*first q := by
  rw [G_filter q hq hq0 0 (by omega), PentagonalOuterSum.filtered_zero_product q hq hq0]
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  unfold first
  field_simp [EulerGaussianLimit.euler_ne_zero (q^5) hq5]

theorem G_second_filter (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    (∑ j : Fin 5, zeta^(-((2*j.val:ℕ):ℤ))*G (zeta^j.val*q))= -5*second q := by
  rw [G_filter q hq hq0 2 (by omega), PentagonalOuterSum.filtered_two_product q hq hq0]
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  unfold second
  field_simp [EulerGaussianLimit.euler_ne_zero (q^5) hq5]

theorem first_value (q : ℂ) (hq : ‖q‖ < 1) : Converges firstSeries q (first q) := by
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  exact converges_expand 5 (by omega) (converges_pow (RogersFormalProducts.first_value (q^5) hq5) 2)

theorem second_value (q : ℂ) (hq : ‖q‖ < 1) : Converges secondSeries q (second q) := by
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  exact converges_mul (converges_X_pow q 2)
    (converges_expand 5 (by omega) (converges_pow (RogersFormalProducts.second_value (q^5) hq5) 2))

end
end Borwein.FifthRootOuter
