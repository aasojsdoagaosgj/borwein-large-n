import Borwein.CertifiedInitialRange
import Borwein.CertifiedInteriorSign
import Borwein.CertifiedEndpointSign

set_option autoImplicit false

namespace Borwein.CertifiedLargeN
noncomputable section
open CombinedPhaseSign EndpointStrongConstants EndpointCoefficientConnection

theorem sigma_signed_positive (a : Fin 3) : 0 < sigma a*sign a.val := by
  have hs0 := Real.sqrt_nonneg (5:ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  fin_cases a <;> norm_num [sigma, sign] <;> nlinarith

theorem strong_sign_transfer (a : Fin 3) (c : ℝ) (hc : 0 < sigma a*c) :
    0 < sign a.val*c := by
  have hs : sign a.val*sign a.val=1 := by
    unfold sign
    split_ifs <;> norm_num
  apply (mul_pos_iff_of_pos_left (sigma_signed_positive a)).mp
  calc
    (sigma a*sign a.val)*(sign a.val*c)=sigma a*(sign a.val*sign a.val)*c := by ring
    _ = sigma a*c := by rw [hs, mul_one]
    _ > 0 := hc

theorem half_sign (n m : ℕ) (hn : 31147 ≤ n) (hm : m ≤ 5*n^2) :
    0 ≤ sign (m%5)*((Borwein.polynomial n).coeff m:ℝ) := by
  by_cases hlo : m ≤ 5*n
  · exact CertifiedInitialRange.coefficient_sign n m hlo
  have hn0 : 0 < n := by omega
  have hden : (0:ℝ) < 5*(n:ℝ)^2 := by positivity
  have hU : (m:ℝ)/(5*(n:ℝ)^2) ≤ 1 := by
    apply (div_le_one hden).mpr
    exact_mod_cast hm
  by_cases hL : -RadialDerivatives.firstDerivative (11/2) ≤ (m:ℝ)/(5*(n:ℝ)^2)
  · exact (CertifiedInteriorSign.coefficient_sign_of_ratio n m hn hL hU).le
  have hband : (m:ℝ)/(5*(n:ℝ)^2) ≤ -deriv PhaseIntegral.radialR (11/2) := by
    rw [RadialDerivatives.deriv_radialR]
    exact le_of_lt (lt_of_not_ge hL)
  by_cases ha : m%5 < 3
  · let a : Fin 3 := ⟨m%5,ha⟩
    exact (strong_sign_transfer a _
      (CertifiedEndpointSign.global_strong_sign a n m hn (by omega) rfl hband)).le
  have hweak : m%5=3 ∨ m%5=4 := by have hh := Nat.mod_lt m (by omega : 0 < 5); omega
  have hnegative : (Borwein.polynomial n).coeff m ≤ 0 := by
    by_cases hhi : m < 10*n
    · exact CertifiedFirstTail.window_nonpositive n m (by omega) hhi hweak
    · have hshift : shiftedIndex n m/(5*(n:ℝ)^2) ≤ -deriv PhaseIntegral.radialR (11/2) := by
        apply le_trans _ hband
        apply div_le_div_of_nonneg_right _ hden.le
        unfold shiftedIndex
        have h5 : (0:ℝ) ≤ ((5*n:ℕ):ℝ) := by positivity
        linarith
      exact (CertifiedEndpointSign.global_weak_sign (m%5) n m hn (by omega) rfl hweak hshift).le
  have hm0 : m%5 ≠ 0 := by omega
  simp only [sign, if_neg hm0, neg_one_mul]
  have hr : ((Borwein.polynomial n).coeff m:ℝ) ≤ 0 := by exact_mod_cast hnegative
  linarith

theorem half_integer_sign (n m : ℕ) (hn : 31147 ≤ n) (hm : m ≤ 5*n^2) :
    0 ≤ (if 5 ∣ m then (1:ℤ) else -1)*(Borwein.polynomial n).coeff m := by
  have hh := half_sign n m hn hm
  unfold sign at hh
  by_cases hd : 5 ∣ m
  · have hz : m%5=0 := Nat.mod_eq_zero_of_dvd hd
    simp only [hz, reduceIte, one_mul] at hh
    simp only [if_pos hd, one_mul]
    exact_mod_cast hh
  · have hz : m%5 ≠ 0 := by omega
    simp only [if_neg hz, neg_one_mul] at hh
    simp only [if_neg hd, neg_one_mul]
    exact_mod_cast hh

/-- The Borwein sign assertion for every coefficient and every n above the analytic threshold. -/
theorem coefficient_sign (n m : ℕ) (hn : 31147 ≤ n) :
    0 ≤ (if 5 ∣ m then (1:ℤ) else -1)*(Borwein.polynomial n).coeff m := by
  by_cases hdeg : m ≤ totalDegree n
  · by_cases hm : m ≤ 5*n^2
    · exact half_integer_sign n m hn hm
    · have href := half_integer_sign n (totalDegree n-m) hn (by unfold totalDegree at *; omega)
      rw [sign_class_reflection n m hdeg, ← coeff_reflection n m hdeg] at href
      exact href
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_polynomial]; omega), mul_zero]

end
end Borwein.CertifiedLargeN
