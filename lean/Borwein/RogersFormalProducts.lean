import Borwein.HyperSeriesValue
import Borwein.RogersProducts

set_option autoImplicit false

namespace Borwein.RogersFormalProducts
noncomputable section
open Complex PowerSeries FormalSeriesValue HyperSeriesValue RogersProducts EndpointEta

theorem converges_zero (f : ℤ⟦X⟧) : Converges f 0 ((coeff 0 f:ℤ):ℂ) := by
  have he : term f 0=(fun k : ℕ => if k=0 then ((coeff 0 f:ℤ):ℂ) else 0) := by
    funext k
    by_cases hk : k=0 <;> simp [term, hk]
  unfold Converges
  rw [he]
  constructor
  · simpa only [apply_ite, norm_zero] using (hasSum_ite_eq 0 ‖((coeff 0 f:ℤ):ℂ)‖).summable
  · exact hasSum_ite_eq 0 ((coeff 0 f:ℤ):ℂ)

theorem first_value (q : ℂ) (hq : ‖q‖ < 1) :
    Converges (rrSeries 1) q ((residue q 1*residue q 4)⁻¹) := by
  by_cases hq0 : q=0
  · subst q
    rw [← hyperSeries_eq_rrSeries 1 (by omega)]
    simpa [coeff_zero_hyperSeries, residue, RogersProductLimit.infiniteProduct] using
      converges_zero (hyperSeries 1)
  · have hh := converges_rrSeries q hq 1 (by omega)
    simpa only [Nat.sub_self, first_identity q hq hq0] using hh

theorem second_value (q : ℂ) (hq : ‖q‖ < 1) :
    Converges (rrSeries 2) q ((residue q 2*residue q 3)⁻¹) := by
  by_cases hq0 : q=0
  · subst q
    rw [← hyperSeries_eq_rrSeries 2 (by omega)]
    simpa [coeff_zero_hyperSeries, residue, RogersProductLimit.infiniteProduct] using
      converges_zero (hyperSeries 2)
  · have hh := converges_rrSeries q hq 2 (by omega)
    norm_num only [show 2-1=1 by omega] at hh
    rwa [second_identity q hq hq0] at hh

theorem product_value (q : ℂ) (hq : ‖q‖ < 1) :
    Converges (rrSeries 1*rrSeries 2) q (euler (q^5)/euler q) := by
  have hh := converges_mul (first_value q hq) (second_value q hq)
  have he : (residue q 1*residue q 4)⁻¹*(residue q 2*residue q 3)⁻¹=
      euler (q^5)/euler q := by
    rw [RogersProducts.euler_split q hq]
    have hq5 : ‖q^5‖ < 1 := by rw [Complex.norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
    field_simp [EulerGaussianLimit.euler_ne_zero (q^5) hq5,
      residue_ne_zero q hq 1 (by omega), residue_ne_zero q hq 2 (by omega),
      residue_ne_zero q hq 3 (by omega), residue_ne_zero q hq 4 (by omega)]
  rwa [he] at hh

end
end Borwein.RogersFormalProducts
