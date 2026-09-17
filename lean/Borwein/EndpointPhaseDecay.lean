import Borwein.EndpointTaylor
import Borwein.ExponentialSegment

set_option autoImplicit false

namespace Borwein.EndpointPhaseDecay
noncomputable section
open Complex EndpointPhaseAtoms EndpointPhaseDerivatives EndpointActualPhase
  EndpointSaddleIdentification EndpointDerivativeConstants EndpointTaylor

def gaussian (n : ℕ) (v y : ℝ) : ℂ := -(y:ℂ)^2/2*f2 n v 0

theorem pole_real_difference (v y : ℝ) (hv : 0 < v) :
    ((A:ℂ)*atom 0 0 v y-(A:ℂ)*atom 0 0 v 0).re = -A*y^2/(v*(v^2+y^2)) := by
  have hv0 := ne_of_gt hv
  have hd : v^2+y^2 ≠ 0 := ne_of_gt (by positivity)
  simp [atom, coordinate, Complex.mul_re, Complex.div_re, Complex.normSq_apply]
  field_simp
  ring

theorem phase_real_split (n : ℕ) (v y : ℝ) (hv : 0 < v) :
    (phase n v y).re = -A*y^2/(v*(v^2+y^2))+
      (q0 n v y-q0 n v 0-I*(y:ℂ)*q1 n v 0).re := by
  have he : phase n v y = ((A:ℂ)*atom 0 0 v y-(A:ℂ)*atom 0 0 v 0)+
      I*(y:ℂ)*(A:ℂ)*atom 0 1 v 0+(q0 n v y-q0 n v 0-I*(y:ℂ)*q1 n v 0) := by
    unfold phase f0 f1
    ring
  have hz : (I*(y:ℂ)*(A:ℂ)*atom 0 1 v 0).re=0 := by
    simp [atom, coordinate, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  rw [he, Complex.add_re, Complex.add_re, hz, add_zero, pole_real_difference v y hv]

theorem pole_decay (v y : ℝ) (hv : 0 < v) (hy : |y| ≤ 3*v/4) :
    -A*y^2/(v*(v^2+y^2)) ≤ -(16*A/25)*(y^2/v^3) := by
  have hA : 0 ≤ A := by linarith [A_bounds.1]
  have hs : y^2 ≤ (9/16:ℝ)*v^2 := by nlinarith [sq_abs y, abs_nonneg y]
  have hm := mul_le_mul_of_nonneg_left hs hv.le
  have hd : v*(v^2+y^2) ≤ (25/16:ℝ)*v^3 := by nlinarith
  have hh := div_le_div_of_nonneg_left (mul_nonneg hA (sq_nonneg y)) (by positivity : 0 < v*(v^2+y^2)) hd
  have he : A*y^2/((25/16)*v^3)=(16*A/25)*(y^2/v^3) := by ring
  rw [he] at hh
  rw [neg_mul, neg_div]
  linarith

theorem phase_decay (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hy : |y| ≤ 3*v/4) :
    (phase n v y).re ≤ -(97/1000)*(y^2/v^3) := by
  have hr := (Complex.re_le_norm _).trans (correction_remainder n v y hn hv hτ)
  have hp := pole_decay v y hv hy
  have hc : (97/1000:ℝ) ≤ 16*A/25-71/1000 := by linarith [A_bounds.1]
  have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ y^2/v^3)
  rw [phase_real_split n v y hv]
  have he : (71/1000:ℝ)*y^2/v^3=(71/1000)*(y^2/v^3) := by ring
  rw [he] at hr
  nlinarith

theorem gaussian_real (n : ℕ) (v y : ℝ) : (gaussian n v y).re = -(y^2/2)*(f2 n v 0).re := by
  simp [gaussian, ← Complex.ofReal_pow, Complex.mul_re, Complex.div_re]
  ring

theorem gaussian_decay (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    (gaussian n v y).re ≤ -(97/1000)*(y^2/v^3) := by
  have hF : (38/100)/v^3 ≤ (f2 n v 0).re :=
    (div_le_iff₀ (by positivity : 0 < v^3)).mpr (by nlinarith [(second_main_bounds n v hn hv hτ).1])
  have hh := mul_le_mul_of_nonneg_left hF (by positivity : 0 ≤ y^2/2)
  rw [gaussian_real]
  have he : y^2/2*((38/100)/v^3)=(19/100)*(y^2/v^3) := by ring
  rw [he] at hh
  have hx : 0 ≤ y^2/v^3 := by positivity
  nlinarith

theorem exponential_remainder (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hy : |y| ≤ 3*v/4) :
    ‖exp (phase n v y)-exp (gaussian n v y)‖ ≤
      ((64/25)*|y|^3/(6*v^4))*Real.exp (-(97/1000)*(y^2/v^3)) := by
  have hh := ExponentialSegment.difference_bound (phase n v y) (gaussian n v y)
    (-(97/1000)*(y^2/v^3)) (phase_decay n v y hn hv hτ hy) (gaussian_decay n v y hn hv hτ)
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have he : phase n v y-gaussian n v y=phase n v y+(y:ℂ)^2/2*f2 n v 0 := by unfold gaussian; ring
  rw [he]
  exact phase_remainder n v y hn hv hτ

end
end Borwein.EndpointPhaseDecay
