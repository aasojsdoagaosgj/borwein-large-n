import Borwein.EndpointOuterIntegral

set_option autoImplicit false

namespace Borwein.EndpointConditionalSign
noncomputable section
open Complex EndpointGaussianIntegral EndpointMainArcConnection EndpointCoefficientConnection
  EndpointCircleFunctions EndpointOuterTransfer

theorem strong_budget (a : Fin 3) (n m : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (ha : m%5=a.val)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=(m:ℝ)/(5*(n:ℝ)^2))
    (hG : GMinorBound v) :
    ‖(((Borwein.polynomial n).coeff m:ℂ)*(2*Real.pi:ℂ))/
      (EndpointRootCancellation.constant a.val*center n (m:ℝ) v*(normalizer n v:ℂ))-1‖ ≤ (177/200:ℝ) := by
  have hh := strong_coefficient_error a n m v hn hv hV hτ ha hs
  have hb := EndpointOuterIntegral.strong_ratio_bound a n m v hn hv hV hτ hG
  linarith

theorem weak_budget (a n m : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (ha : m%5=a) (hA : a=3 ∨ a=4)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=shiftedIndex n m/(5*(n:ℝ)^2))
    (hG : GMinorBound v) (hZ : GIntegral m v=0) :
    ‖(((Borwein.polynomial n).coeff m:ℂ)*(2*Real.pi:ℂ))/
      ((-center n (shiftedIndex n m) v)*(normalizer n v:ℂ))-1‖ ≤ (177/200:ℝ) := by
  have hh := weak_coefficient_error_of_G_zero a n m v hn hv hV hτ ha hA hs hZ
  have hb := EndpointOuterIntegral.weak_ratio_bound n m v hn hv hV hτ hG
  linarith

theorem sign_of_relative_error (c : ℤ) (s P : ℝ) (hP : 0 < P)
    (h : ‖((c:ℂ)*(2*Real.pi:ℂ))/((s:ℂ)*(P:ℂ))-1‖ < 1) : 0 < s*(c:ℝ) := by
  have he : ((c:ℂ)*(2*Real.pi:ℂ))/((s:ℂ)*(P:ℂ))-1 =
      ((((c:ℝ)*(2*Real.pi)/(s*P)-1:ℝ)):ℂ) := by push_cast; ring
  rw [he, Complex.norm_real, Real.norm_eq_abs] at h
  have hp : 0 < (c:ℝ)*(2*Real.pi)/(s*P) := by have hh := (abs_lt.mp h).1; linarith
  rcases div_pos_iff.mp hp with ⟨hc,hs⟩ | ⟨hc,hs⟩
  · have hc' : 0 < (c:ℝ) := by nlinarith [Real.pi_pos]
    have hs' : 0 < s := by nlinarith
    exact mul_pos hs' hc'
  · have hc' : (c:ℝ) < 0 := by nlinarith [Real.pi_pos]
    have hs' : s < 0 := by nlinarith
    exact mul_pos_of_neg_of_neg hs' hc'

/-- Conditional endpoint sign: the analytic G minor-arc bound remains an explicit input. -/
theorem strong_sign (a : Fin 3) (n m : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (ha : m%5=a.val)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=(m:ℝ)/(5*(n:ℝ)^2))
    (hG : GMinorBound v) : 0 < EndpointStrongConstants.sigma a*((Borwein.polynomial n).coeff m:ℝ) := by
  have hb := strong_budget a n m v hn hv hV hτ ha hs hG
  rw [EndpointStrongConstants.constant_sigma, center_real n (m:ℝ) v hn hv] at hb
  have hJ := normalizer_pos n v hn hv
  apply sign_of_relative_error ((Borwein.polynomial n).coeff m) (EndpointStrongConstants.sigma a)
    (Real.exp ((n:ℝ)*PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)+(m:ℝ)*v-v/6)*normalizer n v) (by positivity)
  have hh := hb.trans_lt (by norm_num : (177/200:ℝ) < 1)
  simpa only [Complex.ofReal_mul, mul_assoc] using hh

/-- The weak sign additionally requires the actual G coefficient integral to vanish. -/
theorem weak_sign (a n m : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (ha : m%5=a) (hA : a=3 ∨ a=4)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=shiftedIndex n m/(5*(n:ℝ)^2))
    (hG : GMinorBound v) (hZ : GIntegral m v=0) : (Borwein.polynomial n).coeff m < 0 := by
  have hb := weak_budget a n m v hn hv hV hτ ha hA hs hG hZ
  rw [center_real n (shiftedIndex n m) v hn hv] at hb
  have hJ := normalizer_pos n v hn hv
  have hs' : 0 < (-1:ℝ)*((Borwein.polynomial n).coeff m:ℝ) := by
    apply sign_of_relative_error ((Borwein.polynomial n).coeff m) (-1)
      (Real.exp ((n:ℝ)*PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)+shiftedIndex n m*v-v/6)*normalizer n v) (by positivity)
    have hh := hb.trans_lt (by norm_num : (177/200:ℝ) < 1)
    simpa only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, neg_mul, one_mul] using hh
  have hc : ((Borwein.polynomial n).coeff m:ℝ) < 0 := by linarith
  exact_mod_cast hc

end
end Borwein.EndpointConditionalSign
