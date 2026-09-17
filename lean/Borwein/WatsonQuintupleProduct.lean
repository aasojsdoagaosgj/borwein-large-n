import Borwein.WatsonSumLimit
import Borwein.RogersProducts

set_option autoImplicit false

namespace Borwein.WatsonQuintupleProduct
noncomputable section
open Complex EndpointEta EulerGaussianLimit RogersProductLimit RogersProducts
  WatsonThetaExponent WatsonSumLimit WatsonFiniteIdentity WatsonSpecialization Filter
open scoped Topology

theorem residue_shift (x : ℂ) (hx : ‖x‖ < 1) (s : ℕ) :
    residue x s=(1-x^s)*residue x (s+5) := by
  have hx5 : ‖x^5‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  have he : (fun j : ℕ => 1+(-x^s)*(x^5)^(j+1))=
      (fun j : ℕ => 1+(-x^(s+5))*(x^5)^j) := by
    funext j
    rw [pow_succ, pow_add]
    ring
  have hm : Multipliable (fun j : ℕ => 1+(-x^s)*(x^5)^(j+1)) := by
    rw [he]
    exact product_multipliable (x^5) (-x^(s+5)) hx5
  have hh := tprod_eq_zero_mul' (f := fun j : ℕ => 1+(-x^s)*(x^5)^j) hm
  rw [he] at hh
  simpa only [residue, infiniteProduct, pow_zero, mul_one, sub_eq_add_neg] using hh

theorem rhs_tendsto (x : ℂ) (hx : ‖x‖ < 1) (hx0 : x ≠ 0)
    (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ 2) :
    Tendsto (rhs (x^5) ((x^r)⁻¹)) atTop
      (𝓝 ((1-x^(5-2*r))/(residue x r*residue x (5-r)))) := by
  have hx5 : ‖x^5‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  obtain ⟨hA,hB,hC,hD⟩ := parameters x hx0 r hr
  have hw : ((x^r)⁻¹)^2*x^5=x^(5-2*r) := by
    have hs : (x^r)^2*x^(5-2*r)=x^5 := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    have hi : ((x^r)⁻¹)^2=((x^r)^2)⁻¹ := by rw [inv_pow]
    rw [hi, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero _ (pow_ne_zero _ hx0))]
    exact hs.symm
  have hh := (tendsto_const_nhds (x := 1-x^(5-2*r))).div
    ((product_limit (x^5) (-x^r) hx5).mul (product_limit (x^5) (-x^(5-r)) hx5))
    (mul_ne_zero (residue_ne_zero x hx r (by omega))
      (residue_ne_zero x hx (5-r) (by omega)))
  unfold WatsonFiniteIdentity.rhs
  simp only [hw, hC, hD, residue]
  exact hh

theorem normalized_identity (x : ℂ) (hx : ‖x‖ < 1) (hx0 : x ≠ 0)
    (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ 2) :
    normalizer x r*(∑' k : ℤ, term x r k)=
      (1-x^(5-2*r))/(residue x r*residue x (5-r)) := by
  have hl := sum_tendsto x hx hx0 r hr0 hr
  have he : (fun n : ℕ => ∑' k : ℤ, WatsonFiniteTerms.row (x^5) ((x^r)⁻¹) n k)=
      rhs (x^5) ((x^r)⁻¹) := funext (finite_specialization x hx hx0 r hr0 hr)
  rw [he] at hl
  exact tendsto_nhds_unique hl (rhs_tendsto x hx hx0 r hr0 hr)

theorem quintuple_product (x : ℂ) (hx : ‖x‖ < 1) (hx0 : x ≠ 0)
    (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ 2) :
    (∑' k : ℤ, term x r k)=euler (x^5)*residue x (2*r)*residue x (5-2*r)/
      (residue x r*residue x (5-r)) := by
  have hx5 : ‖x^5‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  have hn : (euler (x^5)*residue x (2*r)*residue x (10-2*r))*normalizer x r=1 := by
    unfold normalizer WatsonPochhammerLimit.limit
    change (euler (x^5)*residue x (2*r)*residue x (10-2*r))*
      (euler (x^5)*(euler (x^5)*residue x (2*r))⁻¹*
        (euler (x^5)*residue x (10-2*r))⁻¹)=1
    field_simp [euler_ne_zero (x^5) hx5, residue_ne_zero x hx (2*r) (by omega),
      residue_ne_zero x hx (10-2*r) (by omega)]
  have hs := residue_shift x hx (5-2*r)
  rw [show 5-2*r+5=10-2*r by omega] at hs
  calc
    _ = (euler (x^5)*residue x (2*r)*residue x (10-2*r))*
        (normalizer x r*(∑' k : ℤ, term x r k)) := by rw [← mul_assoc, hn, one_mul]
    _ = euler (x^5)*residue x (2*r)*
        ((1-x^(5-2*r))*residue x (10-2*r))/(residue x r*residue x (5-r)) := by
      rw [normalized_identity x hx hx0 r hr0 hr]
      ring
    _ = _ := by rw [← hs]

theorem first_product (x : ℂ) (hx : ‖x‖ < 1) (hx0 : x ≠ 0) :
    (∑' k : ℤ, term x 1 k)=euler x*((residue x 1*residue x 4)⁻¹)^2 := by
  rw [quintuple_product x hx hx0 1 (by omega) (by omega)]
  norm_num
  rw [euler_split x hx]
  field_simp [residue_ne_zero x hx 1 (by omega), residue_ne_zero x hx 4 (by omega)]

theorem second_product (x : ℂ) (hx : ‖x‖ < 1) (hx0 : x ≠ 0) :
    (∑' k : ℤ, term x 2 k)=euler x*((residue x 2*residue x 3)⁻¹)^2 := by
  rw [quintuple_product x hx hx0 2 (by omega) (by omega)]
  norm_num
  rw [euler_split x hx]
  field_simp [residue_ne_zero x hx 2 (by omega), residue_ne_zero x hx 3 (by omega)]

end
end Borwein.WatsonQuintupleProduct
