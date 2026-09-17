import Borwein.FormalCoefficientIntegral
import Borwein.StableCoefficientIntegral
import Borwein.EndpointWeakIntegralZero

set_option autoImplicit false

namespace Borwein.StableFilterCoefficient
noncomputable section
open Complex PowerSeries MeasureTheory EndpointCircleKernel EndpointCircleFunctions
  StableBorweinSeries FormalSeriesValue FivePoleCircle

theorem shifted_kernel_sum (F : ℂ → ℂ) (c : ℤ) (m : ℕ)
    (hfilter : ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 →
      (∑ j : Fin 5, zeta^(-(((m%5)*j.val:ℕ):ℤ))*EndpointEta.G (zeta^j.val*q))=
        5*(c:ℂ)*F q)
    (v θ : ℝ) (hv : 0 < v) :
    (∑ j : Fin 5, EndpointCircleKernel.kernel EndpointEta.G m v (θ+angle j.val))=
      5*(c:ℂ)*EndpointCircleKernel.kernel F m v θ := by
  have hq : ‖point v θ‖ < 1 := by rw [point_norm]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hq0 : point v θ ≠ 0 := exp_ne_zero _
  simp_rw [EndpointWeakIntegralZero.shifted_kernel]
  rw [← Finset.sum_mul, hfilter (point v θ) hq hq0]
  unfold EndpointCircleKernel.kernel
  ring

theorem integral_of_filter (F : ℂ → ℂ) (c : ℤ) (m : ℕ)
    (hfilter : ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 →
      (∑ j : Fin 5, zeta^(-(((m%5)*j.val:ℕ):ℤ))*EndpointEta.G (zeta^j.val*q))=
        5*(c:ℂ)*F q)
    (v : ℝ) (hv : 0 < v) :
    GIntegral m v=(c:ℂ)*(∫ θ in (0:ℝ)..2*Real.pi, EndpointCircleKernel.kernel F m v θ) := by
  have hC := kernel_continuous EndpointEta.G m v (G_continuous v hv)
  have hi (j : Fin 5) : IntervalIntegrable
      (fun θ => EndpointCircleKernel.kernel EndpointEta.G m v (θ+angle j.val)) volume 0 (2*Real.pi) :=
    (hC.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have he := congrArg (fun f : ℝ → ℂ => ∫ θ in (0:ℝ)..2*Real.pi, f θ)
    (funext (fun θ => shifted_kernel_sum F c m hfilter v θ hv))
  rw [intervalIntegral.integral_finset_sum (fun j _ => hi j)] at he
  simp_rw [EndpointWeakIntegralZero.integral_shift (EndpointCircleKernel.kernel EndpointEta.G m v)
    _ (kernel_periodic EndpointEta.G m v)] at he
  rw [intervalIntegral.integral_const_mul] at he
  change (∑ _j : Fin 5, GIntegral m v)=_ at he
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at he
  linear_combination (1/5:ℂ)*he

theorem coefficient_of_filter (f : ℤ⟦X⟧) (F : ℂ → ℂ) (c : ℤ) (m : ℕ)
    (hF : ∀ q : ℂ, ‖q‖ < 1 → Converges f q (F q))
    (hfilter : ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 →
      (∑ j : Fin 5, zeta^(-(((m%5)*j.val:ℕ):ℤ))*EndpointEta.G (zeta^j.val*q))=
        5*(c:ℂ)*F q) : stableCoeff m=c*coeff m f := by
  have he := integral_of_filter F c m hfilter 1 (by norm_num)
  rw [← StableCoefficientIntegral.stable_integral m 1 (by norm_num),
    FormalCoefficientIntegral.integral_value f F hF m 1 (by norm_num)] at he
  have hpi : (2*Real.pi:ℂ) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hc : (stableCoeff m:ℂ)=(c:ℂ)*((coeff m f:ℤ):ℂ) := by
    apply mul_right_cancel₀ hpi
    rw [mul_assoc]
    exact he
  exact_mod_cast hc

end
end Borwein.StableFilterCoefficient
