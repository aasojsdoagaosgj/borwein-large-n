import Borwein.FirstOrderTailProduct
import Borwein.CertifiedLowWeakZero

set_option autoImplicit false

namespace Borwein.StableFirstTail
noncomputable section
open StableBorweinSeries FirstOrderTailProduct

def tailCoefficient (n m : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (m+1), ∑ a : Fin 4,
    if Borwein.exponent (n+i) a ≤ m then
      stableCoeff (m-Borwein.exponent (n+i) a) else 0

theorem shifted_stable (n m i : ℕ) (a : Fin 4) (hm : m < 10*n+2) :
    shiftedCoeff (Borwein.polynomial n) m (Borwein.exponent (n+i) a) =
      if Borwein.exponent (n+i) a ≤ m then
        stableCoeff (m-Borwein.exponent (n+i) a) else 0 := by
  unfold shiftedCoeff
  split_ifs with h
  · exact (stableCoeff_eq n _ (by unfold Borwein.exponent at *; omega)).symm
  · rfl

theorem coefficient_decomposition (n m : ℕ) (hm : m < 10*n+2) :
    (Borwein.polynomial n).coeff m = stableCoeff m+tailCoefficient n m := by
  have he := first_tail_coefficient n (m+1) m hm
  rw [← stableCoeff_eq (n+(m+1)) m (by omega)] at he
  have hs : (∑ i ∈ Finset.range (m+1), ∑ a : Fin 4,
      shiftedCoeff (Borwein.polynomial n) m (Borwein.exponent (n+i) a)) =
        tailCoefficient n m := by
    unfold tailCoefficient
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    exact shifted_stable n m i a hm
  rw [hs] at he
  linarith

theorem weak_first_tail (n m : ℕ) (hm : m < 10*n+2) (ha : m%5=3 ∨ m%5=4) :
    (Borwein.polynomial n).coeff m = tailCoefficient n m := by
  rw [coefficient_decomposition n m hm, CertifiedLowWeakZero.stable_weak_zero m ha, zero_add]

theorem original_first_tail_window (n K a : ℕ) (hK : K < n) (ha : a=3 ∨ a=4) :
    (Borwein.polynomial n).coeff (5*n+5*K+a) = tailCoefficient n (5*n+5*K+a) :=
  weak_first_tail n (5*n+5*K+a) (by omega) (by omega)

end
end Borwein.StableFirstTail
