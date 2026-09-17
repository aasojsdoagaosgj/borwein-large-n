import Borwein.StableMiddleCoefficient

set_option autoImplicit false

namespace Borwein.CertifiedLowMiddle
noncomputable section
open PowerSeries Finset StableBorweinSeries StableMiddleCoefficient

theorem product_coefficient_pos (j : ℕ) : 0 < coeff j (rrSeries 1*rrSeries 2) := by
  rw [coeff_mul]
  have hterms : ∀ p ∈ antidiagonal j,
      0 ≤ coeff p.1 (rrSeries 1)*coeff p.2 (rrSeries 2) := by
    intro p hp
    exact mul_nonneg (coeffNonneg_rrSeries 1 p.1) (coeffNonneg_rrSeries 2 p.2)
  have hle := Finset.single_le_sum (s := antidiagonal j)
    (f := fun p => coeff p.1 (rrSeries 1)*coeff p.2 (rrSeries 2))
    hterms (mem_antidiagonal.mpr (by simp) : (j,0) ∈ antidiagonal j)
  have hfirst : 0 < coeff j (rrSeries 1) := by
    by_cases hj : j=0
    · subst j; rw [constantCoeff_rrSeries 1 (by omega)]; norm_num
    · exact coeff_rrSeries_pos_of_pos_le 1 j (by omega) (by omega)
  have hp : 0 < coeff j (rrSeries 1)*coeff 0 (rrSeries 2) := by
    rw [constantCoeff_rrSeries 2 (by omega), mul_one]
    exact hfirst
  exact hp.trans_le hle

theorem stable_class_one_negative (j : ℕ) : stableCoeff (5*j+1) < 0 := by
  rw [stable_class_one]
  exact neg_neg_of_pos (product_coefficient_pos j)

/-- All initial coefficients in residue class one are strictly negative. -/
theorem low_middle_sign (n m : ℕ) (hm : m ≤ 5*n) (ha : m%5=1) :
    (Borwein.polynomial n).coeff m < 0 := by
  rw [← stableCoeff_eq n m hm, show m=5*(m/5)+1 by omega]
  exact stable_class_one_negative (m/5)

theorem first_class_one (n j : ℕ) (hj : j < n) :
    (Borwein.polynomial n).coeff (5*j+1) < 0 :=
  low_middle_sign n (5*j+1) (by omega) (by omega)

end
end Borwein.CertifiedLowMiddle
