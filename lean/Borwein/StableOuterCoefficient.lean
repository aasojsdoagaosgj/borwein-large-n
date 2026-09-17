import Borwein.FifthRootOuter
import Borwein.StableFilterCoefficient

set_option autoImplicit false

namespace Borwein.StableOuterCoefficient
noncomputable section
open Complex PowerSeries StableBorweinSeries FifthRootOuter

theorem stable_first (m : ℕ) (hm : m%5=0) : stableCoeff m=coeff m firstSeries := by
  have hh := StableFilterCoefficient.coefficient_of_filter firstSeries first 1 m first_value
    (fun q hq hq0 => by simpa only [hm, Int.cast_one, mul_one] using G_first_filter q hq hq0)
  simpa only [one_mul] using hh

theorem stable_second (m : ℕ) (hm : m%5=2) : stableCoeff m= -coeff m secondSeries := by
  have hh := StableFilterCoefficient.coefficient_of_filter secondSeries second (-1) m second_value
    (fun q hq hq0 => by simpa only [hm, Int.cast_neg, Int.cast_one, mul_neg_one] using G_second_filter q hq hq0)
  simpa only [neg_one_mul] using hh

theorem first_coefficient (j : ℕ) : coeff (5*j) firstSeries=coeff j ((rrSeries 1)^2) := by
  unfold firstSeries
  rw [coeff_expand]
  simp

theorem second_coefficient (j : ℕ) : coeff (5*j+2) secondSeries=coeff j ((rrSeries 2)^2) := by
  unfold secondSeries
  rw [coeff_X_pow_mul', if_pos (by omega), show 5*j+2-2=5*j by omega, coeff_expand]
  simp

theorem stable_class_zero (j : ℕ) : stableCoeff (5*j)=coeff j ((rrSeries 1)^2) := by
  rw [stable_first (5*j) (by omega), first_coefficient]

theorem stable_class_two (j : ℕ) : stableCoeff (5*j+2)= -coeff j ((rrSeries 2)^2) := by
  rw [stable_second (5*j+2) (by omega), second_coefficient]

end
end Borwein.StableOuterCoefficient
