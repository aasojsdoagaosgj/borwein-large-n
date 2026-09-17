import Borwein.EndpointEta

set_option autoImplicit false

namespace Borwein.EndpointPositiveCusp
noncomputable section
open Complex EndpointEta
open scoped Real

theorem sqrt_scale (r : ℝ) (z : ℂ) (hr : 0 < r) (hz : z ≠ 0) :
    sqrt ((r:ℂ)*z) = (Real.sqrt r:ℂ)*sqrt z := by
  have hr0 : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hs : sqrt (r:ℂ) = (Real.sqrt r:ℂ) := by
    rw [sqrt, Real.sqrt_eq_rpow, Complex.ofReal_cpow hr.le]
    congr 1
    norm_num
  rw [sqrt_eq_exp (mul_ne_zero hr0 hz), Complex.log_ofReal_mul hr hz,
    add_div, Complex.exp_add, Complex.ofReal_log hr.le, ← sqrt_eq_exp hr0,
    ← sqrt_eq_exp hz, hs]

theorem G_inversion (z : ℂ) (hz : 0 < z.im) :
    G (q (-1/z)) = (Real.sqrt 5:ℂ)*
      exp ((Real.pi:ℂ)*I*(z/15-1/(3*z))) * (euler (q z)/euler (q (z/5))) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hz5 : 0 < (z/5).im := by simpa using div_pos hz (by norm_num : (0:ℝ)<5)
  have hz50 : z/5 ≠ 0 := div_ne_zero hz0 (by norm_num)
  have hs5 : sqrt z = (Real.sqrt 5:ℂ)*sqrt (z/5) := by
    convert sqrt_scale 5 (z/5) (by norm_num) hz50 using 1 <;> norm_num <;> congr 1 <;> ring
  have hs0 : sqrt (z/5) ≠ 0 := by rw [sqrt_eq_exp hz50]; exact Complex.exp_ne_zero _
  have hIsqrt : sqrt I ≠ 0 := by
    rw [sqrt_eq_exp I_ne_zero]
    exact Complex.exp_ne_zero _
  unfold G
  rw [← q_five]
  have harg : 5*(-1/z) = -1/(z/5) := by field_simp <;> ring
  rw [harg, euler_inversion z hz, euler_inversion (z/5) hz5]
  rw [mul_div_mul_comm, mul_div_mul_comm, ← Complex.exp_sub, hs5]
  have hratio : (sqrt I)⁻¹*((Real.sqrt 5:ℂ)*sqrt (z/5))/
      ((sqrt I)⁻¹*sqrt (z/5)) = (Real.sqrt 5:ℂ) := by
    field_simp [hIsqrt]
  rw [hratio]
  have hex : (Real.pi:ℂ)*I*(z+1/z)/12-(Real.pi:ℂ)*I*(z/5+1/(z/5))/12 =
      (Real.pi:ℂ)*I*(z/15-1/(3*z)) := by field_simp <;> ring
  rw [hex]

def transformedPoint (w : ℂ) : ℂ := 2*Real.pi*I/w

theorem transformedPoint_im (w : ℂ) :
    (transformedPoint w).im = 2*Real.pi*w.re/Complex.normSq w := by
  simp [transformedPoint, Complex.div_im]

theorem transformedPoint_upper (w : ℂ) (hw : 0 < w.re) :
    0 < (transformedPoint w).im := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  rw [transformedPoint_im]
  exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hw)
    (Complex.normSq_pos.mpr hw0)

/-- Manuscript (5.5), with the exact infinite-product correction on the right half-plane. -/
theorem positive_cusp (w : ℂ) (hw : 0 < w.re) :
    G (exp (-w)) = (Real.sqrt 5:ℂ)*
      exp (-(2*(Real.pi:ℂ)^2/15)/w-w/6) *
        (euler (exp (-4*(Real.pi:ℂ)^2/w))/
          euler (exp (-4*(Real.pi:ℂ)^2/(5*w)))) := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have hp0 : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hq : q (-1/transformedPoint w) = exp (-w) := by
    unfold q transformedPoint
    congr 1
    field_simp
  have hq1 : q (transformedPoint w) = exp (-4*(Real.pi:ℂ)^2/w) := by
    unfold q transformedPoint
    congr 1
    field_simp
    ring_nf
    simp [I_sq]
  have hq5 : q (transformedPoint w/5) = exp (-4*(Real.pi:ℂ)^2/(5*w)) := by
    unfold q transformedPoint
    congr 1
    field_simp
    ring_nf
    simp [I_sq]
  have hex : (Real.pi:ℂ)*I*(transformedPoint w/15-1/(3*transformedPoint w)) =
      -(2*(Real.pi:ℂ)^2/15)/w-w/6 := by
    unfold transformedPoint
    field_simp
    ring_nf
    simp [I_sq]
  simpa only [hq, hq1, hq5, hex] using G_inversion (transformedPoint w) (transformedPoint_upper w hw)

end
end Borwein.EndpointPositiveCusp
