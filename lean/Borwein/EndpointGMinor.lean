import Borwein.InverseEulerAngularDecay
import Borwein.InverseEulerRadialBound
import Borwein.EulerGaussianBound
import Borwein.EndpointRangeSign

set_option autoImplicit false

namespace Borwein.EndpointGMinor
noncomputable section
open Complex PeriodicRadialProfile EndpointCircleKernel EndpointOuterGeometry
  EndpointGaussianIntegral EndpointActualPhase

theorem fifth_angle_away (v t : ℝ) (haway : outside (width v) t) :
    ∀ k : ℤ, 3*(5*v)/4 ≤ |5*t-(k:ℝ)*(2*Real.pi)| := by
  intro k
  have he := mul_le_mul_of_nonneg_left (haway k) (by norm_num : (0:ℝ) ≤ 5)
  have hi : 5*t-(k:ℝ)*(2*Real.pi) = 5*(t-2*Real.pi*(k:ℝ)/5) := by ring
  rw [hi, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<5)]
  dsimp [width] at he
  linarith

theorem exponent_budget (v : ℝ) (hv : 0 < v) :
    Real.pi^2/(30*v)-(11/100)/v ≤ A/v-1/(25*v) := by
  have hp : Real.pi^2 ≤ 21/2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  unfold A
  apply (mul_le_mul_iff_of_pos_right hv).mp
  field_simp
  nlinarith

theorem actual_bound (v t : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000)
    (haway : outside (width v) t) :
    ‖EndpointEta.G (point v t)‖ ≤ 6*Real.exp (A/v-1/(25*v)) := by
  have hq0 : ray v t ≠ 0 := Complex.exp_ne_zero _
  have hnum := EulerGaussianBound.euler_small_radius (ray v t) v hv hV hq0 (ray_norm v t)
  have hdec := InverseEulerAngularDecay.full_angle_decay (5*v) (5*t)
    (by positivity) (by linarith) (fifth_angle_away v t haway)
  have hrad := InverseEulerRadialBound.inverse_radial (5*v) (by positivity) (by linarith)
  have hp : ray v t^5 = ray (5*v) (5*t) := by simpa [ray] using ray_power v t 5
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hs5 : Real.sqrt (5*v) = Real.sqrt 5*Real.sqrt v := Real.sqrt_mul (by norm_num) _
  have hcoeff : (2/Real.sqrt v)*Real.sqrt (5*v) = 2*Real.sqrt 5 := by
    rw [hs5]
    field_simp
  have hex : Real.pi^2/(6*(5*v)) + -(11/20)/(5*v) =
      Real.pi^2/(30*v)-(11/100)/v := by ring
  have hC : 2*Real.sqrt 5 ≤ 6 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
  change ‖EndpointEta.G (ray v t)‖ ≤ _
  rw [EndpointEta.G, div_eq_mul_inv, norm_mul, hp]
  calc
    _ ≤ (2/Real.sqrt v)*(‖(EndpointEta.euler (ray (5*v) (5*t)))⁻¹‖) :=
      mul_le_mul_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (2/Real.sqrt v)*((Real.sqrt (5*v)*Real.exp (Real.pi^2/(6*(5*v))))*
        Real.exp (-(11/20)/(5*v))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hdec.trans (mul_le_mul_of_nonneg_right hrad (Real.exp_pos _).le)
    _ = (2*Real.sqrt 5)*Real.exp (Real.pi^2/(30*v)-(11/100)/v) := by
      rw [← mul_assoc, ← mul_assoc, hcoeff, mul_assoc, ← Real.exp_add, hex]
    _ ≤ 6*Real.exp (A/v-1/(25*v)) := mul_le_mul hC
      (Real.exp_le_exp.mpr (exponent_budget v hv)) (Real.exp_pos _).le (by norm_num)

theorem GMinorBound (v : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000) :
    EndpointOuterTransfer.GMinorBound v := by
  intro t ht
  exact actual_bound v t hv hV ht

end
end Borwein.EndpointGMinor
