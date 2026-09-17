import Borwein.CoprimeNonresonantBound
import Borwein.DilogarithmUpper

set_option autoImplicit false

namespace Borwein.WeightedResidueBound
noncomputable section
open ZeroPoleBudget DilogarithmUpper

theorem reciprocal_perturbation (r x e w D : ℝ) (hr : 1 ≤ r) (hx : 0 ≤ x)
    (he0 : 0 ≤ e) (he : e < 1) (hxe : x ≤ e) (hD : 0 ≤ D) (hw : w*x ≤ D) :
    w/(r-x) ≤ w/r+D/((1-e)*r^2) := by
  have hr0 : 0 < r := by linarith
  have hc : 0 < 1-e := by linarith
  have hlow : r*(1-e) ≤ r-x := by nlinarith
  have hden : (1-e)*r^2 ≤ r*(r-x) := by nlinarith
  have hden0 : 0 < (1-e)*r^2 := by positivity
  have hden1 : 0 < r*(r-x) := hden0.trans_le hden
  have hdiff : r-x ≠ 0 := ne_of_gt (by nlinarith : 0 < r-x)
  have hid : w/(r-x) = w/r+(w*x)/(r*(r-x)) := by field_simp [hr0.ne',hdiff]; ring
  rw [hid]
  exact add_le_add le_rfl ((div_le_div_of_nonneg_right hw hden1.le).trans
    (div_le_div_of_nonneg_left hD hden0 hden))

theorem young (w r : ℝ) : w/r ≤ (w^2+1/r^2)/2 := by
  have h := sq_nonneg (w-r⁻¹)
  simp only [div_eq_mul_inv,← inv_pow]
  norm_num only [one_mul,invOf_eq_inv,inv_eq_one_div] at *
  nlinarith

theorem weight_square (η : ℝ) (k : ℕ) : (weight η k)^2 = (Real.exp (-(2*η)))^k/(k:ℝ)^2 := by
  unfold weight
  rw [div_pow,← Real.exp_nat_mul,← Real.exp_nat_mul]
  congr 1
  congr 1
  ring

theorem square_sum (s : Finset ℕ) (η : ℝ) (hη : 0 ≤ η) :
    (∑ k ∈ s, (weight η k)^2) ≤ radial (2*η) := by
  simp_rw [weight_square]
  have h := Summable.sum_le_tsum s (fun k _ => by positivity)
    (radial_summable (2*η) (by positivity))
  exact h

theorem reciprocal_sum (s : Finset ℕ) (η : ℝ) (r : ℕ → ℝ) (hη : 0 ≤ η) :
    (∑ k ∈ s, weight η k/r k) ≤ radial (2*η)/2+(∑ k ∈ s, (1:ℝ)/(r k)^2)/2 := by
  have h := Finset.sum_le_sum (s := s) (fun k _ => young (weight η k) (r k))
  simp only [add_div,Finset.sum_add_distrib,← Finset.sum_div] at h
  linarith [square_sum s η hη]

theorem perturbed_sum (s : Finset ℕ) (η : ℝ) (Q K d : ℕ) (r : ℕ → ℝ)
    (hη : 0 ≤ η) (hQ : 0 < Q) (hcut : d*K < Q)
    (hk : ∀ k ∈ s, 0 < k ∧ k ≤ K) (hr : ∀ k ∈ s, 1 ≤ r k) :
    (∑ k ∈ s, weight η k/(r k-(d:ℝ)*k/Q)) ≤
      radial (2*η)/2+(1/2+(d:ℝ)/(Q*(1-(d:ℝ)*K/Q)))*(∑ k ∈ s, (1:ℝ)/(r k)^2) := by
  have hQ' : (0:ℝ) < Q := by exact_mod_cast hQ
  have hcut' : (d:ℝ)*K/Q < 1 := (div_lt_one hQ').mpr (by exact_mod_cast hcut)
  have ht (k : ℕ) (hks : k ∈ s) :
      weight η k/(r k-(d:ℝ)*k/Q) ≤ weight η k/r k+
        ((d:ℝ)/(Q*(1-(d:ℝ)*K/Q)))*(1/(r k)^2) := by
    have hc := PoleVariation.fourier_weight_cancellation η hη k (hk k hks).1
    have hw : weight η k*((d:ℝ)*k/Q) ≤ (d:ℝ)/Q := by
      have hm := mul_le_mul_of_nonneg_right hc (div_nonneg (Nat.cast_nonneg d) hQ'.le)
      change (Real.exp (-η*k)/(k:ℝ))*(k:ℝ)*((d:ℝ)/Q) ≤ _ at hm
      convert hm using 1 <;> (try unfold weight) <;> ring
    have hp := reciprocal_perturbation (r k) ((d:ℝ)*k/Q) ((d:ℝ)*K/Q) (weight η k) ((d:ℝ)/Q)
      (hr k hks) (by positivity) (by positivity) hcut'
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast (hk k hks).2) (Nat.cast_nonneg d)) hQ'.le)
      (by positivity) hw
    exact hp.trans_eq (by simp only [div_eq_mul_inv,mul_inv_rev]; ring)
  have h := Finset.sum_le_sum ht
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at h
  have hy := reciprocal_sum s η r hη
  linarith

end
end Borwein.WeightedResidueBound
