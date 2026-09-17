import Borwein.FirstTailBlock

set_option autoImplicit false

namespace Borwein.FirstTailKernel
noncomputable section
open PowerSeries FirstTailBlock

theorem geometric_coefficient (f : ℤ⟦X⟧) (K : ℕ) :
    coeff K (geometricSeries*f)=∑ i ∈ Finset.range (K+1), coeff (K-i) f := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [geometricSeries]

theorem quotient_eq : geometricSeries*numerator= -hypergeometricD := by
  unfold numerator hypergeometricD
  rw [hyperSeries_eq_rrSeries 1 (by omega), hyperSeries_eq_rrSeries 2 (by omega)]
  ring

theorem tail_eq_negative_d (n K a : ℕ) (ha : a=3 ∨ a=4) :
    StableFirstTail.tailCoefficient n (5*n+5*K+a)= -concreteDCoeff K := by
  rw [tail_sum n K a ha, ← geometric_coefficient, quotient_eq, map_neg]
  change -hypergeometricDCoeff K= -concreteDCoeff K
  rw [hypergeometricDCoeff_eq_concreteDCoeff]

/-- The first-tail formula is now about the original finite polynomial. -/
theorem original_coefficient (n K a : ℕ) (hK : K < n) (ha : a=3 ∨ a=4) :
    (Borwein.polynomial n).coeff (5*n+5*K+a)= -concreteDCoeff K := by
  rw [StableFirstTail.original_first_tail_window n K a hK ha, tail_eq_negative_d n K a ha]

end
end Borwein.FirstTailKernel
