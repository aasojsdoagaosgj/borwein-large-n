import Borwein.StableCoefficientIntegral
import Borwein.EndpointWeakIntegralZero

set_option autoImplicit false

namespace Borwein.CertifiedLowWeakZero
noncomputable section
open StableBorweinSeries StableCoefficientIntegral

theorem stable_weak_zero (m : ℕ) (hm : m%5=3 ∨ m%5=4) : stableCoeff m = 0 := by
  have he := stable_integral m 1 (by norm_num)
  rw [EndpointWeakIntegralZero.GIntegral_zero m 1 (by norm_num) hm] at he
  have hp : (2*Real.pi:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0:ℝ)<2*Real.pi))
  have hz : (stableCoeff m:ℂ) = 0 := (mul_eq_zero.mp he).resolve_right hp
  exact_mod_cast hz

theorem low_weak_zero (n m : ℕ) (hm : m ≤ 5*n) (ha : m%5=3 ∨ m%5=4) :
    (Borwein.polynomial n).coeff m = 0 := by
  rw [← stableCoeff_eq n m hm]
  exact stable_weak_zero m ha

theorem first_three_class (n j : ℕ) (hj : j < n) :
    (Borwein.polynomial n).coeff (5*j+3) = 0 :=
  low_weak_zero n (5*j+3) (by omega) (by omega)

theorem first_four_class (n j : ℕ) (hj : j < n) :
    (Borwein.polynomial n).coeff (5*j+4) = 0 :=
  low_weak_zero n (5*j+4) (by omega) (by omega)

theorem series_weak_zero (m : ℕ) (hm : m%5=3 ∨ m%5=4) :
    PowerSeries.coeff m series = 0 := by
  rw [coeff_series]
  exact stable_weak_zero m hm

end
end Borwein.CertifiedLowWeakZero
