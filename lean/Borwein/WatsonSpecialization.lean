import Borwein.WatsonFiniteIdentity

set_option autoImplicit false

namespace Borwein.WatsonSpecialization
noncomputable section
open Complex EndpointEulerTail WatsonFiniteTerms WatsonFiniteIdentity

theorem parameters (x : ℂ) (hx0 : x ≠ 0) (r : ℕ) (hr : r ≤ 2) :
    ((((x^r)⁻¹)^2)⁻¹=x^(2*r)) ∧
    (((x^r)⁻¹)^2*(x^5)^2=x^(10-2*r)) ∧
    (((x^r)⁻¹)⁻¹=x^r) ∧
    ((x^r)⁻¹*x^5=x^(5-r)) := by
  have h10 : (x^r)^2*x^(10-2*r)=x^10 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have h5 : x^r*x^(5-r)=x^5 := by
    rw [← pow_add]
    congr 1
    omega
  refine ⟨?_, ?_, inv_inv _, ?_⟩
  · rw [← inv_pow, inv_inv, ← pow_mul]
    congr 1
    omega
  · have hinv : ((x^r)⁻¹)^2=((x^r)^2)⁻¹ := by rw [inv_pow]
    rw [hinv, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero _ (pow_ne_zero _ hx0))]
    simpa only [← pow_mul, show 5*2=10 by omega] using h10.symm
  · rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero _ hx0)]
    exact h5.symm

theorem positive_factors (x : ℂ) (hx : ‖x‖ < 1) (s : ℕ) (hs : 0 < s) (j : ℕ) :
    1-x^s*(x^5)^j ≠ 0 := by
  rw [← pow_mul, ← pow_add]
  exact factor_ne_zero x hx _ (by omega)

/-- Both parameter choices needed for the remaining Borwein dissection have no singular factors. -/
theorem finite_specialization (x : ℂ) (hx : ‖x‖ < 1) (hx0 : x ≠ 0)
    (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ 2) (n : ℕ) :
    (∑' k : ℤ, row (x^5) ((x^r)⁻¹) n k)=rhs (x^5) ((x^r)⁻¹) n := by
  have hx5 : ‖x^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  obtain ⟨hA,hB,hC,hD⟩ := parameters x hx0 r hr
  apply finite_watson (x^5) ((x^r)⁻¹) hx5 (pow_ne_zero _ hx0) (inv_ne_zero (pow_ne_zero _ hx0))
  · intro j
    rw [hA]
    exact positive_factors x hx (2*r) (by omega) j
  · intro j
    rw [hB]
    exact positive_factors x hx (10-2*r) (by omega) j
  · intro j
    rw [hC]
    exact positive_factors x hx r (by omega) j
  · intro j
    rw [hD]
    exact positive_factors x hx (5-r) (by omega) j

end
end Borwein.WatsonSpecialization
