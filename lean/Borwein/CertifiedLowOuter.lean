import Borwein.CertifiedFiveDissection

set_option autoImplicit false

namespace Borwein.CertifiedLowOuter
noncomputable section
open PowerSeries Finset StableBorweinSeries StableOuterCoefficient

theorem square_coefficient_pos (t j : ℕ) (ht : 0 < t)
    (hj : j=0 ∨ t ≤ j) : 0 < coeff j ((rrSeries t)^2) := by
  rw [pow_two, coeff_mul]
  have hterms : ∀ p ∈ antidiagonal j,
      0 ≤ coeff p.1 (rrSeries t)*coeff p.2 (rrSeries t) := by
    intro p hp
    exact mul_nonneg (coeffNonneg_rrSeries t p.1) (coeffNonneg_rrSeries t p.2)
  have hle := Finset.single_le_sum (s := antidiagonal j)
    (f := fun p => coeff p.1 (rrSeries t)*coeff p.2 (rrSeries t))
    hterms (mem_antidiagonal.mpr (by simp) : (j,0) ∈ antidiagonal j)
  have hfirst : 0 < coeff j (rrSeries t) := by
    rcases hj with rfl | hj
    · rw [constantCoeff_rrSeries t ht]; norm_num
    · exact coeff_rrSeries_pos_of_pos_le t j ht hj
  rw [constantCoeff_rrSeries t ht, mul_one] at hle
  exact hfirst.trans_le hle

theorem second_square_one_zero : coeff 1 ((rrSeries 2)^2)=0 := by
  rw [pow_two, coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have he : p.1+p.2=1 := mem_antidiagonal.mp hp
  have hh : p.1=1 ∨ p.2=1 := by omega
  rcases hh with hh | hh
  · rw [hh, coeff_one_rrSeries_two, zero_mul]
  · rw [hh, coeff_one_rrSeries_two, mul_zero]

theorem stable_class_zero_positive (j : ℕ) : 0 < stableCoeff (5*j) := by
  rw [stable_class_zero]
  exact square_coefficient_pos 1 j (by omega) (by omega)

theorem stable_class_two_negative (j : ℕ) (hj : j ≠ 1) : stableCoeff (5*j+2) < 0 := by
  rw [stable_class_two]
  exact neg_neg_of_pos (square_coefficient_pos 2 j (by omega) (by omega))

theorem stable_seven_zero : stableCoeff 7=0 := by
  have hh := stable_class_two 1
  norm_num only at hh
  rw [hh, second_square_one_zero, neg_zero]

theorem low_zero_sign (n m : ℕ) (hm : m ≤ 5*n) (ha : m%5=0) :
    0 < (Borwein.polynomial n).coeff m := by
  rw [← stableCoeff_eq n m hm, show m=5*(m/5) by omega]
  exact stable_class_zero_positive (m/5)

theorem low_two_sign (n m : ℕ) (hm : m ≤ 5*n) (ha : m%5=2) (h7 : m ≠ 7) :
    (Borwein.polynomial n).coeff m < 0 := by
  rw [← stableCoeff_eq n m hm, show m=5*(m/5)+2 by omega]
  exact stable_class_two_negative (m/5) (by omega)

theorem low_seven_zero (n : ℕ) (hn : 2 ≤ n) : (Borwein.polynomial n).coeff 7=0 := by
  rw [← stableCoeff_eq n 7 (by omega)]
  exact stable_seven_zero

end
end Borwein.CertifiedLowOuter
