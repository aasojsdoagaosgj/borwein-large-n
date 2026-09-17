import Borwein.EndpointMainArcConnection

set_option autoImplicit false

namespace Borwein.EndpointLocalNumericBudget
noncomputable section
open Complex EndpointGaussianIntegral EndpointMainArcConnection

theorem uniform_budget (n : ℕ) (v : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    15*Real.sqrt v+15*EndpointTailGlobalLog.radialX n v+60*v ≤ (681/1000:ℝ) := by
  have hs : Real.sqrt v ≤ (361/10000:ℝ) := by
    have he := Real.sq_sqrt hv.le
    have hp := Real.sqrt_nonneg v
    nlinarith
  have he := EndpointDerivativeConstants.exponential_lower
  have hh := he.trans (Real.exp_le_exp.mpr hτ)
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 24469/100) hh
  have hx : EndpointTailGlobalLog.radialX n v ≤ (100/24469:ℝ) := by
    unfold EndpointTailGlobalLog.radialX
    rw [neg_mul, Real.exp_neg]
    convert! hi using 1 <;> norm_num [one_div]
  linarith

theorem strong_main_budget (a : Fin 3) (n : ℕ) (k v : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    ‖strongIntegral a n k v/(EndpointRootCancellation.constant a.val*center n k v*(normalizer n v:ℂ))-1‖ ≤
      (681/1000:ℝ) :=
  (strong_normalized_bound a n k v hn hv hV hτ hs).trans (uniform_budget n v hv hV hτ)

theorem weak_main_budget (a n : ℕ) (ha : a=3 ∨ a=4) (k v : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    ‖weakIntegral a n k v/((-center n k v)*(normalizer n v:ℂ))-1‖ ≤ (681/1000:ℝ) :=
  (weak_normalized_bound a n ha k v hn hv hV hτ hs).trans (uniform_budget n v hv hV hτ)

end
end Borwein.EndpointLocalNumericBudget
