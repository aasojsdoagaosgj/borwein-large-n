import Borwein.EulerQBinomial

set_option autoImplicit false

namespace Borwein.IntegerQBinomial
noncomputable section
open Complex EulerQBinomial

def choose (q : ℂ) (n : ℕ) (k : ℤ) : ℂ :=
  if 0 ≤ k then gaussian q n k.toNat else 0

theorem choose_nat (q : ℂ) (n k : ℕ) : choose q n k = gaussian q n k := by
  simp [choose]

theorem choose_negative (q : ℂ) (n : ℕ) (k : ℤ) (hk : k < 0) : choose q n k = 0 := by
  simp [choose, not_le.mpr hk]

theorem choose_above (q : ℂ) (n : ℕ) (k : ℤ) (hk : (n:ℤ) < k) : choose q n k = 0 := by
  rw [choose, if_pos (by omega)]
  exact gaussian_outside q n k.toNat (by omega)

theorem choose_zero_column (q : ℂ) (n : ℕ) (hq : ‖q‖ < 1) : choose q n 0 = 1 := by
  rw [← Int.natCast_zero, choose_nat]
  exact gaussian_zero q n hq

theorem choose_zero_row (q : ℂ) (k : ℤ) (hq : ‖q‖ < 1) :
    choose q 0 k = if k=0 then 1 else 0 := by
  split_ifs with hk
  · subst k; exact choose_zero_column q 0 hq
  · rcases lt_or_gt_of_ne hk with h | h
    · exact choose_negative q 0 k h
    · exact choose_above q 0 k h

theorem pascal_left (q : ℂ) (n : ℕ) (k : ℤ) (hq : ‖q‖ < 1) :
    choose q (n+1) k = choose q n (k-1)+q^k*choose q n k := by
  by_cases hk : k < 0
  · rw [choose_negative q (n+1) k hk, choose_negative q n k hk,
      choose_negative q n (k-1) (by omega)]
    ring
  by_cases hk0 : k=0
  · subst k
    rw [choose_zero_column q (n+1) hq, choose_zero_column q n hq,
      choose_negative q n (0-1) (by omega)]
    simp
  obtain ⟨j,hj⟩ : ∃ j : ℕ, k=(j+1:ℕ) := ⟨(k-1).toNat, by omega⟩
  subst k
  rw [show ((j+1:ℕ):ℤ)-1=(j:ℤ) by omega, choose_nat, choose_nat, choose_nat,
    zpow_natCast]
  exact gaussian_succ q n j hq

theorem pascal_right (q : ℂ) (n : ℕ) (k : ℤ) (hq : ‖q‖ < 1) :
    choose q (n+1) k = choose q n k+q^((n:ℤ)+1-k)*choose q n (k-1) := by
  by_cases hk : k < 0
  · rw [choose_negative q (n+1) k hk, choose_negative q n k hk,
      choose_negative q n (k-1) (by omega)]
    ring
  by_cases hk0 : k=0
  · subst k
    rw [choose_zero_column q (n+1) hq, choose_zero_column q n hq,
      choose_negative q n (0-1) (by omega)]
    ring
  by_cases hkn : (n:ℤ)+1 < k
  · rw [choose_above q (n+1) k (by omega), choose_above q n k (by omega),
      choose_above q n (k-1) (by omega)]
    ring
  obtain ⟨j,hj⟩ : ∃ j : ℕ, k=(j+1:ℕ) := ⟨(k-1).toNat, by omega⟩
  subst k
  have hjn : j ≤ n := by omega
  rw [show ((j+1:ℕ):ℤ)-1=(j:ℤ) by omega, choose_nat, choose_nat, choose_nat,
    show (n:ℤ)+1-(j+1:ℕ)=(n-j:ℕ) by omega, zpow_natCast]
  exact gaussian_succ_right q n j hq hjn

end
end Borwein.IntegerQBinomial
