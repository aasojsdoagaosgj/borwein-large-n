import Borwein.FifthRootMiddle
import Borwein.FormalCoefficientIntegral
import Borwein.StableCoefficientIntegral
import Borwein.EndpointWeakIntegralZero

set_option autoImplicit false

namespace Borwein.StableMiddleCoefficient
noncomputable section
open Complex PowerSeries MeasureTheory EndpointCircleKernel EndpointCircleFunctions
  StableBorweinSeries FormalSeriesValue

def middle (q : ℂ) : ℂ := q*(EndpointEta.euler (q^25)/EndpointEta.euler (q^5))
def middleSeries : ℤ⟦X⟧ := X*expand 5 (by omega) (rrSeries 1*rrSeries 2)

theorem middle_value (q : ℂ) (hq : ‖q‖ < 1) : Converges middleSeries q (middle q) :=
  FifthRootMiddle.middle_series_value q hq

theorem shifted_kernel_sum (m : ℕ) (v θ : ℝ) (hv : 0 < v) (hm : m%5=1) :
    (∑ j : Fin 5, EndpointCircleKernel.kernel EndpointEta.G m v (θ+angle j.val))=
      -5*EndpointCircleKernel.kernel middle m v θ := by
  have hq : ‖point v θ‖ < 1 := by rw [point_norm]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hq0 : point v θ ≠ 0 := exp_ne_zero _
  simp_rw [EndpointWeakIntegralZero.shifted_kernel, hm]
  rw [← Finset.sum_mul, FifthRootMiddle.G_middle_filter (point v θ) hq hq0]
  unfold middle EndpointCircleKernel.kernel
  ring

theorem GIntegral_middle (m : ℕ) (v : ℝ) (hv : 0 < v) (hm : m%5=1) :
    GIntegral m v = -(∫ θ in (0:ℝ)..2*Real.pi, EndpointCircleKernel.kernel middle m v θ) := by
  have hC := kernel_continuous EndpointEta.G m v (G_continuous v hv)
  have hi (j : Fin 5) : IntervalIntegrable
      (fun θ => EndpointCircleKernel.kernel EndpointEta.G m v (θ+angle j.val)) volume 0 (2*Real.pi) :=
    (hC.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have he := congrArg (fun f : ℝ → ℂ => ∫ θ in (0:ℝ)..2*Real.pi, f θ)
    (funext (fun θ => shifted_kernel_sum m v θ hv hm))
  rw [intervalIntegral.integral_finset_sum (fun j _ => hi j)] at he
  simp_rw [EndpointWeakIntegralZero.integral_shift (EndpointCircleKernel.kernel EndpointEta.G m v)
    _ (kernel_periodic EndpointEta.G m v)] at he
  rw [intervalIntegral.integral_const_mul] at he
  change (∑ _j : Fin 5, GIntegral m v)=_ at he
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at he
  linear_combination (1/5:ℂ)*he

theorem stable_middle (m : ℕ) (hm : m%5=1) :
    stableCoeff m = -coeff m middleSeries := by
  have he := GIntegral_middle m 1 (by norm_num) hm
  rw [← StableCoefficientIntegral.stable_integral m 1 (by norm_num),
    FormalCoefficientIntegral.integral_value middleSeries middle middle_value m 1 (by norm_num)] at he
  have hpi : (2*Real.pi:ℂ) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hc : (stableCoeff m:ℂ)= -((coeff m middleSeries:ℤ):ℂ) := by
    apply mul_right_cancel₀ hpi
    rw [neg_mul]
    exact he
  exact_mod_cast hc

theorem middle_coefficient (j : ℕ) : coeff (5*j+1) middleSeries=coeff j (rrSeries 1*rrSeries 2) := by
  unfold middleSeries
  rw [show (X:ℤ⟦X⟧)=X^1 by simp, coeff_X_pow_mul', if_pos (by omega),
    show 5*j+1-1=5*j by omega, coeff_expand]
  simp

theorem stable_class_one (j : ℕ) :
    stableCoeff (5*j+1)= -coeff j (rrSeries 1*rrSeries 2) := by
  rw [stable_middle (5*j+1) (by omega), middle_coefficient]

end
end Borwein.StableMiddleCoefficient
