import Borwein.EndpointSaddleIdentification
import Borwein.HigherOrderSegment

set_option autoImplicit false

namespace Borwein.EndpointTaylor
noncomputable section
open Complex Set EndpointPhaseAtoms EndpointPhaseDerivatives EndpointActualPhase
  EndpointSaddleIdentification EndpointDerivativeConstants

def phase (n : ℕ) (v y : ℝ) : ℂ := f0 n v y-f0 n v 0-I*(y:ℂ)*f1 n v 0

theorem quadratic_remainder (g0 g1 g2 : ℝ → ℂ) (C y : ℝ)
    (h0 : ∀ t, HasDerivAt g0 (I*g1 t) t) (h1 : ∀ t, HasDerivAt g1 (I*g2 t) t)
    (h2 : Continuous g2) (hb : ∀ t, ‖g2 t‖ ≤ C) :
    ‖g0 y-g0 0-I*(y:ℂ)*g1 0‖ ≤ C*y^2/2 := by
  let a : ℂ := I*(y:ℂ)
  have hd0 (t : ℝ) : HasDerivAt (fun t => g0 (t*y)) (a*g1 (t*y)) t := by
    convert! (h0 (t*y)).scomp t ((hasDerivAt_id t).mul_const y) using 1 <;>
      simp only [Function.comp_def, Complex.real_smul] <;> dsimp [a] <;> ring
  have hd1 (t : ℝ) : HasDerivAt (fun t => a*g1 (t*y)) (a^2*g2 (t*y)) t := by
    convert! ((h1 (t*y)).scomp t ((hasDerivAt_id t).mul_const y)).const_mul a using 1 <;>
      simp only [Function.comp_def, Complex.real_smul] <;> dsimp [a] <;> ring
  have hc : Continuous (fun t => a^2*g2 (t*y)) := continuous_const.mul (h2.comp (by fun_prop))
  have hn : ‖a^2‖=y^2 := by simp [a, norm_pow, norm_mul, sq_abs]
  have hh := SecondOrderSegment.remainder_bound (fun t => g0 (t*y)) (fun t => a*g1 (t*y))
    (fun t => a^2*g2 (t*y)) (C*y^2) (fun t _ => hd0 t) (fun t _ => hd1 t) hc.continuousOn
    (fun t _ => by rw [norm_mul, hn]; simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb (t*y)) (sq_nonneg y))
  simpa only [mul_one, one_mul, zero_mul, a] using hh

theorem cubic_remainder (g0 g1 g2 g3 : ℝ → ℂ) (C y : ℝ)
    (h0 : ∀ t, HasDerivAt g0 (I*g1 t) t) (h1 : ∀ t, HasDerivAt g1 (I*g2 t) t)
    (h2 : ∀ t, HasDerivAt g2 (I*g3 t) t) (h3 : Continuous g3) (hb : ∀ t, ‖g3 t‖ ≤ C) :
    ‖g0 y-g0 0-I*(y:ℂ)*g1 0+(y:ℂ)^2/2*g2 0‖ ≤ C*|y|^3/6 := by
  let a : ℂ := I*(y:ℂ)
  have hd0 (t : ℝ) : HasDerivAt (fun t => g0 (t*y)) (a*g1 (t*y)) t := by
    convert! (h0 (t*y)).scomp t ((hasDerivAt_id t).mul_const y) using 1 <;>
      simp only [Function.comp_def, Complex.real_smul] <;> dsimp [a] <;> ring
  have hd1 (t : ℝ) : HasDerivAt (fun t => a*g1 (t*y)) (a^2*g2 (t*y)) t := by
    convert! ((h1 (t*y)).scomp t ((hasDerivAt_id t).mul_const y)).const_mul a using 1 <;>
      simp only [Function.comp_def, Complex.real_smul] <;> dsimp [a] <;> ring
  have hd2 (t : ℝ) : HasDerivAt (fun t => a^2*g2 (t*y)) (a^3*g3 (t*y)) t := by
    convert! ((h2 (t*y)).scomp t ((hasDerivAt_id t).mul_const y)).const_mul (a^2) using 1 <;>
      simp only [Function.comp_def, Complex.real_smul] <;> dsimp [a] <;> ring
  have hc : Continuous (fun t => a^3*g3 (t*y)) := continuous_const.mul (h3.comp (by fun_prop))
  have hn : ‖a^3‖=|y|^3 := by simp [a, norm_pow, norm_mul]
  have hh := HigherOrderSegment.cubic_bound (fun t => g0 (t*y)) (fun t => a*g1 (t*y))
    (fun t => a^2*g2 (t*y)) (fun t => a^3*g3 (t*y)) (C*|y|^3)
    (fun t _ => hd0 t) (fun t _ => hd1 t) (fun t _ => hd2 t) hc.continuousOn
    (fun t _ => by rw [norm_mul, hn]; simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb (t*y)) (by positivity : 0 ≤ |y|^3))
  have ha : a^2=-(y:ℂ)^2 := by simp [a, mul_pow, Complex.I_sq]
  simp only [one_mul, zero_mul, ha, Complex.real_smul] at hh
  convert! hh using 1
  congr 1
  dsimp [a]
  push_cast
  ring

theorem correction_remainder (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖q0 n v y-q0 n v 0-I*(y:ℂ)*q1 n v 0‖ ≤ (71/1000)*y^2/v^3 := by
  have hc : Continuous (q2 n v) := continuous_iff_continuousAt.mpr (fun t => (q2_deriv n v t hn hv).continuousAt)
  have hh := quadratic_remainder (q0 n v) (q1 n v) (q2 n v) ((71/500)/v^3) y
    (fun t => q0_deriv n v t hn hv) (fun t => q1_deriv n v t hn hv) hc
    (fun t => (le_div_iff₀ (by positivity : 0 < v^3)).mpr (by nlinarith [second_correction_bound n v t hn hv hτ]))
  exact hh.trans_eq (by ring)

theorem phase_remainder (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖phase n v y+(y:ℂ)^2/2*f2 n v 0‖ ≤ (64/25)*|y|^3/(6*v^4) := by
  have hc : Continuous (f3 n v) := continuous_iff_continuousAt.mpr (fun t => (f3_deriv n v t hn hv).continuousAt)
  have hh := cubic_remainder (f0 n v) (f1 n v) (f2 n v) (f3 n v) ((64/25)/v^4) y
    (fun t => f0_deriv n v t hn hv) (fun t => f1_deriv n v t hn hv)
    (fun t => f2_deriv n v t hn hv) hc
    (fun t => (le_div_iff₀ (by positivity : 0 < v^4)).mpr (by nlinarith [third_main_bound n v t hn hv hτ]))
  exact hh.trans_eq (by ring)

end
end Borwein.EndpointTaylor
