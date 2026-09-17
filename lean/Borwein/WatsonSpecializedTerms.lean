import Borwein.WatsonSpecialization
import Borwein.WatsonThetaExponent

set_option autoImplicit false

namespace Borwein.WatsonSpecializedTerms
noncomputable section
open Complex WatsonThetaExponent WatsonFiniteTerms WatsonPochhammer

theorem weight_power (x : ℂ) (hx0 : x ≠ 0) (r : ℕ) (k : ℤ) :
    WatsonWeights.weight (x^5) ((x^r)⁻¹) k =
      (-1:ℂ)^k*x^(exponent r 0 k) := by
  have hq : (x^5)^(pentagonal (-k):ℤ)=x^(5*(pentagonal (-k):ℤ)) := by
    rw [← zpow_natCast x 5, ← zpow_mul]
    norm_num
  have hw : ((x^r)⁻¹)^(3*k)=x^(-3*(r:ℤ)*k) := by
    rw [inv_zpow, ← zpow_natCast x r, ← zpow_mul, ← zpow_neg]
    congr 1
    ring
  rw [WatsonWeights.weight, hq, hw, mul_assoc, ← zpow_add₀ hx0]
  congr 2
  simp [exponent]
  <;> ring

theorem correction_power (x : ℂ) (hx0 : x ≠ 0) (r : ℕ) (k : ℤ) :
    ((x^r)⁻¹)^2*(x^5)*((x^5)^k)^2=x^(10*k+5-2*(r:ℤ)) := by
  have hw : ((x^r)⁻¹)^2=x^(-2*(r:ℤ)) := by
    rw [← zpow_ofNat _ 2, inv_zpow, ← zpow_natCast x r, ← zpow_mul, ← zpow_neg]
    congr 1
    ring
  have hq : ((x^5)^k)^2=x^(10*k) := by
    rw [← zpow_ofNat _ 2, ← zpow_natCast x 5, ← zpow_mul, ← zpow_mul]
    congr 1
    ring
  rw [hw, hq, ← zpow_natCast x 5, ← zpow_add₀ hx0, ← zpow_add₀ hx0]
  congr 1
  ring

theorem weight_correction (x : ℂ) (hx0 : x ≠ 0) (r : ℕ)
    (hr0 : 1 ≤ r) (hr : r ≤ 2) (k : ℤ) :
    WatsonWeights.weight (x^5) ((x^r)⁻¹) k *
      (1-((x^r)⁻¹)^2*(x^5)*((x^5)^k)^2)=term x r k := by
  rw [weight_power x hx0 r k, correction_power x hx0 r k]
  have he : exponent r 0 k+(10*k+5-2*(r:ℤ))=exponent r 1 k := by
    simp [exponent]
  rw [mul_sub, mul_one, mul_assoc, ← zpow_add₀ hx0, he,
    ← degree_cast r 0 hr0 hr (by omega) k, ← degree_cast r 1 hr0 hr (by omega) k,
    zpow_natCast, zpow_natCast]
  unfold term
  ring

theorem row_eq (x : ℂ) (hx0 : x ≠ 0) (r : ℕ)
    (hr0 : 1 ≤ r) (hr : r ≤ 2) (n : ℕ) (k : ℤ) :
    row (x^5) ((x^r)⁻¹) n k =
      EndpointEulerTail.finiteEuler (2*n) (x^5)*term x r k*
        inverse (x^5) (x^(2*r)) ((n:ℤ)-k)*
        inverse (x^5) (x^(10-2*r)) ((n:ℤ)+k) := by
  obtain ⟨hA,hB,hC,hD⟩ := WatsonSpecialization.parameters x hx0 r hr
  unfold row
  rw [hA, hB, mul_assoc (EndpointEulerTail.finiteEuler (2*n) (x^5)),
    weight_correction x hx0 r hr0 hr k]

end
end Borwein.WatsonSpecializedTerms
