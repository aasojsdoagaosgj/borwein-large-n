import Borwein.FirstTailKernel

set_option autoImplicit false

namespace Borwein.CertifiedFirstTail
noncomputable section
open FirstTailKernel

theorem nonpositive (n K a : ℕ) (hK : K < n) (ha : a=3 ∨ a=4) :
    (Borwein.polynomial n).coeff (5*n+5*K+a) ≤ 0 := by
  rw [original_coefficient n K a hK ha]
  exact neg_nonpos.mpr (concreteDCoeff_nonneg K)

theorem negative (n K a : ℕ) (hK : K < n) (ha : a=3 ∨ a=4) (h1 : K ≠ 1) :
    (Borwein.polynomial n).coeff (5*n+5*K+a) < 0 := by
  rw [original_coefficient n K a hK ha]
  by_cases h0 : K=0
  · subst K
    rw [concreteDCoeff_zero]
    norm_num
  · exact neg_neg_of_pos (concreteDCoeff_pos K (by omega))

theorem zero_iff (n K a : ℕ) (hK : K < n) (ha : a=3 ∨ a=4) :
    (Borwein.polynomial n).coeff (5*n+5*K+a)=0 ↔ K=1 := by
  constructor
  · intro hz
    by_contra h1
    have hn := negative n K a hK ha h1
    omega
  · intro h1
    subst K
    rw [original_coefficient n 1 a hK ha, concreteDCoeff_one, neg_zero]

theorem first_value (n a : ℕ) (hn : 0 < n) (ha : a=3 ∨ a=4) :
    (Borwein.polynomial n).coeff (5*n+a)= -1 := by
  have hh := original_coefficient n 0 a hn ha
  simpa only [Nat.mul_zero, Nat.add_zero, concreteDCoeff_zero] using hh

theorem exceptional_eight (n : ℕ) (hn : 2 ≤ n) :
    (Borwein.polynomial n).coeff (5*n+8)=0 := by
  have hh := (zero_iff n 1 3 (by omega) (by omega)).mpr rfl
  convert hh using 1 <;> congr 1 <;> omega

theorem exceptional_nine (n : ℕ) (hn : 2 ≤ n) :
    (Borwein.polynomial n).coeff (5*n+9)=0 := by
  have hh := (zero_iff n 1 4 (by omega) (by omega)).mpr rfl
  convert hh using 1 <;> congr 1 <;> omega

theorem window_nonpositive (n m : ℕ) (hlo : 5*n ≤ m) (hhi : m < 10*n)
    (ha : m%5=3 ∨ m%5=4) : (Borwein.polynomial n).coeff m ≤ 0 := by
  have hm : m=5*n+5*((m-5*n)/5)+m%5 := by omega
  rw [hm]
  exact nonpositive n ((m-5*n)/5) (m%5) (by omega) ha

theorem window_negative (n m : ℕ) (hlo : 5*n ≤ m) (hhi : m < 10*n)
    (ha : m%5=3 ∨ m%5=4) (h8 : m ≠ 5*n+8) (h9 : m ≠ 5*n+9) :
    (Borwein.polynomial n).coeff m < 0 := by
  have hm : m=5*n+5*((m-5*n)/5)+m%5 := by omega
  rw [hm]
  exact negative n ((m-5*n)/5) (m%5) (by omega) ha (by omega)

end
end Borwein.CertifiedFirstTail
