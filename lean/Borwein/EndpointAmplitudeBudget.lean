import Borwein.EndpointAmplitudeContinuity
import Borwein.EndpointAbsoluteIntegral

set_option autoImplicit false

namespace Borwein.EndpointAmplitudeBudget
noncomputable section
open Complex Set EndpointPhaseAtoms EndpointAmplitudeContinuity EndpointGaussianIntegral

def rotation (y : ℝ) : ℂ := exp (-I*(y:ℂ)/6)
def adjusted (ε : ℝ → ℂ) (y : ℝ) : ℂ := rotation y*(1+ε y)

theorem coordinate_box_norm (v y : ℝ) (hv : 0 < v) (hy : |y| ≤ 3*v/4) :
    ‖coordinate v y‖ ≤ 5*v/4 := by
  have hs : ‖coordinate v y‖^2=v^2+y^2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, coordinate, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im,
      Complex.mul_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one]
    ring
  have hys : |y|^2 ≤ (3*v/4)^2 := (sq_le_sq₀ (abs_nonneg y) (by positivity)).mpr hy
  rw [sq_abs] at hys
  have hp := norm_nonneg (coordinate v y)
  nlinarith

theorem rotation_norm (y : ℝ) : ‖rotation y‖=1 := by
  rw [rotation, Complex.norm_exp]
  simp

theorem rotation_error (y : ℝ) : ‖rotation y-1‖ ≤ |y|/6 := by
  have hh := ExponentialSegment.difference_bound (-I*(y:ℂ)/6) 0 0 (by simp) (by simp)
  simpa [rotation, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs] using hh

theorem adjusted_continuous (ε : ℝ → ℂ) (hε : Continuous ε) : Continuous (adjusted ε) := by
  have hr : Continuous rotation := by unfold rotation; fun_prop
  exact hr.mul (continuous_const.add hε)

theorem adjusted_error (ε : ℝ → ℂ) (X v y : ℝ) (hv : 0 < v) (hy : |y| ≤ 3*v/4)
    (hε : ‖ε y‖ ≤ 8*X+25*‖coordinate v y‖) :
    ‖adjusted ε y-1‖ ≤ 8*X+32*v := by
  have he : adjusted ε y-1=(rotation y-1)+rotation y*ε y := by unfold adjusted; ring
  rw [he]
  have hh := norm_add_le (rotation y-1) (rotation y*ε y)
  rw [norm_mul, rotation_norm, one_mul] at hh
  have hr := rotation_error y
  have hw := coordinate_box_norm v y hv hy
  linarith

theorem strong_error_bound (a : Fin 3) (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hy : |y| ≤ 3*v/4) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖strongError a n v y‖ ≤ 8*EndpointTailGlobalLog.radialX n v+25*‖coordinate v y‖ := by
  have hh := EndpointStrongPolynomial.main_relative_error a n (coordinate v y) hn
    (by simpa [coordinate] using hv) (by simpa [coordinate] using hy)
    (EndpointWeakTail.box_x_norm n v y hτ) (EndpointWeakTail.box_norm v y hv hV hy)
  simpa [strongError, EndpointFiniteTailExpansion.x_norm, coordinate, EndpointTailGlobalLog.radialX] using hh

theorem weak_error_bound (a n : ℕ) (ha : a=3 ∨ a=4) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hy : |y| ≤ 3*v/4) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖weakError a n v y‖ ≤ 8*EndpointTailGlobalLog.radialX n v+25*‖coordinate v y‖ := by
  have hh := EndpointWeakTail.normalized_error a n ha (coordinate v y) hn
    (by simpa [coordinate] using hv) (by simpa [coordinate] using hy)
    (EndpointWeakTail.box_x_norm n v y hτ) (EndpointWeakTail.box_norm v y hv hV hy)
  simpa [weakError, EndpointFiniteTailExpansion.x_norm, coordinate, EndpointTailGlobalLog.radialX] using hh

end
end Borwein.EndpointAmplitudeBudget
