import Borwein.CertifiedLargeN
import Borwein.ExplicitLargeNZeroSet

set_option autoImplicit false

namespace Borwein.CertifiedLargeNZeroHalf
noncomputable section

open CombinedPhaseSign EndpointCoefficientConnection ExplicitLargeNZeroSet

/-- Every listed lower zero is an exact zero, already for `n >= 2`.
This direction uses only the stable coefficients and the first-tail identity. -/
theorem coefficient_zero_of_mem (n m : ℕ) (hn : 2 ≤ n)
    (hm : m ∈ lowerZeros n) : (Borwein.polynomial n).coeff m = 0 := by
  rcases (mem_lowerZeros n m).mp hm with h | h | h | h
  · exact CertifiedLowWeakZero.low_weak_zero n m h.2.le h.1
  · subst m
    exact CertifiedLowOuter.low_seven_zero n hn
  · subst m
    exact CertifiedFirstTail.exceptional_eight n hn
  · subst m
    exact CertifiedFirstTail.exceptional_nine n hn

/-- Outside the explicit lower zero set, the existing large-n estimates
give strict signed positivity on the entire lower half. No finite-run
certificate or new numerical bound is used. -/
theorem strict_sign_of_not_mem (n m : ℕ) (hn : 31147 ≤ n)
    (hm : m ≤ 5*n^2) (hnot : m ∉ lowerZeros n) :
    0 < sign (m%5)*((Borwein.polynomial n).coeff m : ℝ) := by
  have h7 : m ≠ 7 := by
    intro h
    exact hnot ((mem_lowerZeros n m).mpr (Or.inr (Or.inl h)))
  have h8 : m ≠ 5*n+8 := by
    intro h
    exact hnot ((mem_lowerZeros n m).mpr (Or.inr (Or.inr (Or.inl h))))
  have h9 : m ≠ 5*n+9 := by
    intro h
    exact hnot ((mem_lowerZeros n m).mpr (Or.inr (Or.inr (Or.inr h))))
  by_cases hlo : m ≤ 5*n
  · have ha : m%5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases h : m%5
    · have hh := CertifiedLowOuter.low_zero_sign n m hlo h
      simp only [sign, h, reduceIte, one_mul]
      exact_mod_cast hh
    · have hh := CertifiedLowMiddle.low_middle_sign n m hlo h
      have hr : ((Borwein.polynomial n).coeff m : ℝ) < 0 := by exact_mod_cast hh
      norm_num only [sign, h, Nat.one_ne_zero, if_false, neg_one_mul]
      linarith
    · have hh := CertifiedLowOuter.low_two_sign n m hlo h h7
      have hr : ((Borwein.polynomial n).coeff m : ℝ) < 0 := by exact_mod_cast hh
      norm_num only [sign, h, OfNat.ofNat_ne_zero, if_false, neg_one_mul]
      linarith
    · exact (hnot ((mem_lowerZeros n m).mpr
        (Or.inl ⟨Or.inl h, by omega⟩))).elim
    · exact (hnot ((mem_lowerZeros n m).mpr
        (Or.inl ⟨Or.inr h, by omega⟩))).elim
  have hn0 : 0 < n := by omega
  have hden : (0 : ℝ) < 5*(n : ℝ)^2 := by positivity
  have hU : (m : ℝ)/(5*(n : ℝ)^2) ≤ 1 := by
    apply (div_le_one hden).mpr
    exact_mod_cast hm
  by_cases hL : -RadialDerivatives.firstDerivative (11/2) ≤
      (m : ℝ)/(5*(n : ℝ)^2)
  · exact CertifiedInteriorSign.coefficient_sign_of_ratio n m hn hL hU
  have hband : (m : ℝ)/(5*(n : ℝ)^2) ≤ -deriv PhaseIntegral.radialR (11/2) := by
    rw [RadialDerivatives.deriv_radialR]
    exact le_of_lt (lt_of_not_ge hL)
  by_cases ha : m%5 < 3
  · let a : Fin 3 := ⟨m%5, ha⟩
    exact CertifiedLargeN.strong_sign_transfer a _
      (CertifiedEndpointSign.global_strong_sign a n m hn (by omega) rfl hband)
  have hweak : m%5=3 ∨ m%5=4 := by
    have hh := Nat.mod_lt m (by norm_num : 0 < 5)
    omega
  have hnegative : (Borwein.polynomial n).coeff m < 0 := by
    by_cases hhi : m < 10*n
    · exact CertifiedFirstTail.window_negative n m (by omega) hhi hweak h8 h9
    · have hshift : shiftedIndex n m/(5*(n : ℝ)^2) ≤
          -deriv PhaseIntegral.radialR (11/2) := by
        apply le_trans _ hband
        apply div_le_div_of_nonneg_right _ hden.le
        unfold shiftedIndex
        have h5 : (0 : ℝ) ≤ ((5*n : ℕ) : ℝ) := by positivity
        linarith
      exact CertifiedEndpointSign.global_weak_sign (m%5) n m hn
        (by omega) rfl hweak hshift
  have hm0 : m%5 ≠ 0 := by omega
  simp only [sign, if_neg hm0, neg_one_mul]
  have hr : ((Borwein.polynomial n).coeff m : ℝ) < 0 := by exact_mod_cast hnegative
  linarith

/-- The manuscript's exact lower-half zero classification in its stated
analytic range. The upper half and the cardinality are separate set lemmas. -/
theorem zero_iff (n m : ℕ) (hn : 31147 ≤ n) (hm : m ≤ 5*n^2) :
    (Borwein.polynomial n).coeff m = 0 ↔ m ∈ lowerZeros n := by
  constructor
  · intro hz
    by_contra hnot
    have hs := strict_sign_of_not_mem n m hn hm hnot
    rw [hz, Int.cast_zero, mul_zero] at hs
    exact (lt_irrefl (0 : ℝ)) hs
  · exact coefficient_zero_of_mem n m (by omega)

end
end Borwein.CertifiedLargeNZeroHalf
