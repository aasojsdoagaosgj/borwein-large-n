import Borwein.CertifiedFirstTail
import Borwein.CertifiedLowOuter
import Borwein.CertifiedLowMiddle
import Borwein.CombinedPhaseSign

set_option autoImplicit false

namespace Borwein.CertifiedInitialRange
noncomputable section
open CombinedPhaseSign

theorem coefficient_sign (n m : ℕ) (hm : m ≤ 5*n) :
    0 ≤ sign (m%5)*((Borwein.polynomial n).coeff m:ℝ) := by
  have ha : m%5 < 5 := Nat.mod_lt _ (by omega)
  interval_cases h : m%5
  · have hh := CertifiedLowOuter.low_zero_sign n m hm h
    simp only [sign, reduceIte, one_mul]
    exact_mod_cast hh.le
  · have hh := CertifiedLowMiddle.low_middle_sign n m hm h
    norm_num only [sign, Nat.one_ne_zero, if_false, neg_one_mul]
    have hr : ((Borwein.polynomial n).coeff m:ℝ) ≤ 0 := by exact_mod_cast hh.le
    linarith
  · by_cases h7 : m=7
    · subst m
      rw [CertifiedLowOuter.low_seven_zero n (by omega), Int.cast_zero, mul_zero]
    · have hh := CertifiedLowOuter.low_two_sign n m hm h h7
      norm_num only [sign, OfNat.ofNat_ne_zero, if_false, neg_one_mul]
      have hr : ((Borwein.polynomial n).coeff m:ℝ) ≤ 0 := by exact_mod_cast hh.le
      linarith
  · rw [CertifiedLowWeakZero.low_weak_zero n m hm (by omega), Int.cast_zero, mul_zero]
  · rw [CertifiedLowWeakZero.low_weak_zero n m hm (by omega), Int.cast_zero, mul_zero]

end
end Borwein.CertifiedInitialRange
