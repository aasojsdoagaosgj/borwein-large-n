import Borwein.CertifiedLargeNZeroHalf

set_option autoImplicit false

namespace Borwein.CertifiedLargeNZeroSet
noncomputable section
open ExplicitLargeNZeroSet

/-- Only coefficients within the degree of the polynomial belong to its
finite zero set. Coefficients beyond that degree are not counted. -/
def coefficientZeros (n : ℕ) : Finset ℕ :=
  (Finset.range (totalDegree n+1)).filter
    (fun m => (Borwein.polynomial n).coeff m = 0)

theorem zeros_le_degree (n : ℕ) (hn : 2 ≤ n) {m : ℕ}
    (hm : m ∈ zeros n) : m ≤ totalDegree n := by
  rw [zeros, Finset.mem_union] at hm
  rcases hm with hm | hm
  · have hhalf := lowerZeros_lt_half n hn hm
    unfold totalDegree
    omega
  · rcases Finset.mem_image.mp hm with ⟨k, _, rfl⟩
    exact Nat.sub_le _ _

/-- The full coefficient-zero classification in work theorem A, including
the reflected upper half, for the original analytic threshold. -/
theorem coefficient_zero_iff (n m : ℕ) (hn : 31147 ≤ n)
    (hm : m ≤ totalDegree n) :
    (Borwein.polynomial n).coeff m = 0 ↔ m ∈ zeros n := by
  rw [zeros, Finset.mem_union]
  constructor
  · intro hz
    by_cases hhalf : m ≤ 5*n^2
    · exact Or.inl ((CertifiedLargeNZeroHalf.zero_iff n m hn hhalf).mp hz)
    · have hrefHalf : totalDegree n-m ≤ 5*n^2 := by
        unfold totalDegree at *
        omega
      have hrefZero : (Borwein.polynomial n).coeff (totalDegree n-m) = 0 := by
        rw [← coeff_reflection n m hm]
        exact hz
      have hrefMem :=
        (CertifiedLargeNZeroHalf.zero_iff n (totalDegree n-m) hn hrefHalf).mp hrefZero
      apply Or.inr
      apply Finset.mem_image.mpr
      refine ⟨totalDegree n-m, hrefMem, ?_⟩
      unfold totalDegree at *
      omega
  · intro hz
    rcases hz with hz | hz
    · exact CertifiedLargeNZeroHalf.coefficient_zero_of_mem n m (by omega) hz
    · rcases Finset.mem_image.mp hz with ⟨k, hk, rfl⟩
      have hkHalf := lowerZeros_lt_half n (by omega) hk
      have hkDegree : k ≤ totalDegree n := by
        unfold totalDegree
        omega
      change (Borwein.polynomial n).coeff (totalDegree n-k) = 0
      rw [← coeff_reflection n k hkDegree]
      exact CertifiedLargeNZeroHalf.coefficient_zero_of_mem n k (by omega) hk

theorem zero_set_eq (n : ℕ) (hn : 31147 ≤ n) : coefficientZeros n = zeros n := by
  ext m
  simp only [coefficientZeros, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨hm, hz⟩
    exact (coefficient_zero_iff n m hn hm).mp hz
  · intro hz
    have hm := zeros_le_degree n (by omega) hz
    exact ⟨hm, (coefficient_zero_iff n m hn hm).mpr hz⟩

theorem zero_count (n : ℕ) (hn : 31147 ≤ n) : (coefficientZeros n).card = 4*n+6 := by
  rw [zero_set_eq n hn]
  exact zeros_card n (by omega)

end
end Borwein.CertifiedLargeNZeroSet
