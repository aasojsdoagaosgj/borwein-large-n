import Borwein.EndpointFiveLocalArcs
import Borwein.CoefficientArcSplit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false

namespace Borwein.EndpointCircleKernel
noncomputable section
open Complex EndpointPhaseAtoms FivePoleCircle

def angle (j : ℕ) : ℝ := 2*Real.pi*j/5
def point (v θ : ℝ) : ℂ := exp (-(v:ℂ)+(θ:ℂ)*I)
def kernel (F : ℂ → ℂ) (m : ℕ) (v θ : ℝ) : ℂ :=
  F (point v θ)*exp ((m:ℂ)*((v:ℂ)-(θ:ℂ)*I))
def weighted (F : ℂ → ℂ) (a : ℕ) (v y : ℝ) : ℂ := ∑ j : Fin 5,
  zeta^(-((a*j.val:ℕ):ℤ))*F (zeta^j.val*exp (-coordinate v y))

theorem point_norm (v θ : ℝ) : ‖point v θ‖=Real.exp (-v) := by
  rw [point, Complex.norm_exp]
  simp

theorem point_continuous (v : ℝ) : Continuous (point v) := by unfold point; fun_prop

theorem point_periodic (v : ℝ) : Function.Periodic (point v) (2*Real.pi) := by
  intro θ
  unfold point
  have he : -(v:ℂ)+((θ+2*Real.pi:ℝ):ℂ)*I=(-(v:ℂ)+(θ:ℂ)*I)+2*(Real.pi:ℂ)*I := by push_cast; ring
  rw [he, exp_add, exp_two_pi_mul_I, mul_one]

theorem kernel_periodic (F : ℂ → ℂ) (m : ℕ) (v : ℝ) :
    Function.Periodic (kernel F m v) (2*Real.pi) := by
  intro θ
  rw [kernel, point_periodic v θ]
  have he : (m:ℂ)*((v:ℂ)-((θ+2*Real.pi:ℝ):ℂ)*I)=
      (m:ℂ)*((v:ℂ)-(θ:ℂ)*I)+(-((m:ℤ):ℂ))*(2*Real.pi*I) := by push_cast; ring
  rw [he, exp_add]
  have hz : exp ((-((m:ℤ):ℂ))*(2*Real.pi*I))=1 := by
    convert! exp_int_mul_two_pi_mul_I (-(m:ℤ)) using 1 <;> push_cast <;> ring
  rw [hz, mul_one]
  rfl

theorem kernel_continuous (F : ℂ → ℂ) (m : ℕ) (v : ℝ)
    (hF : Continuous (fun θ => F (point v θ))) : Continuous (kernel F m v) := by
  exact hF.mul (by fun_prop)

theorem root_angle (j : ℕ) : exp ((angle j:ℂ)*I)=zeta^j := by
  unfold zeta
  rw [AngularKernel.circle_eq_exp, ← exp_nat_mul]
  congr 1
  unfold angle
  push_cast
  ring

theorem rotated_point (j : ℕ) (v y : ℝ) : point v (angle j-y)=zeta^j*exp (-coordinate v y) := by
  rw [← root_angle, ← exp_add]
  unfold point coordinate
  congr 1
  push_cast
  ring

theorem phase_weight (j m : ℕ) : exp (-(m:ℂ)*(angle j:ℂ)*I)=zeta^(-(((m%5)*j:ℕ):ℤ)) := by
  have he : -(m:ℂ)*(angle j:ℂ)*I=-((m:ℂ)*((angle j:ℂ)*I)) := by ring
  rw [he, exp_neg, exp_nat_mul, root_angle, zpow_neg, zpow_natCast]
  have hp : (zeta^j)^m=(zeta^m)^j := by simp only [← pow_mul]; rw [Nat.mul_comm]
  rw [hp, SaddleArcConnection.fifth_power_reduction zeta zeta_primitive.pow_eq_one m, pow_mul]

theorem rotated_kernel (F : ℂ → ℂ) (j m : ℕ) (v y : ℝ) :
    kernel F m v (angle j-y)=zeta^(-(((m%5)*j:ℕ):ℤ))*F (zeta^j*exp (-coordinate v y))*
      exp ((m:ℂ)*coordinate v y) := by
  unfold kernel
  rw [rotated_point]
  have he : (m:ℂ)*((v:ℂ)-((angle j-y:ℝ):ℂ)*I)=
      -(m:ℂ)*(angle j:ℂ)*I+(m:ℂ)*coordinate v y := by unfold coordinate; push_cast; ring
  rw [he, exp_add, phase_weight]
  ring

theorem sum_rotated (F : ℂ → ℂ) (m : ℕ) (v y : ℝ) :
    (∑ j : Fin 5, kernel F m v (angle j.val-y))=weighted F (m%5) v y*exp ((m:ℂ)*coordinate v y) := by
  simp_rw [rotated_kernel]
  exact (Finset.sum_mul ..).symm

end
end Borwein.EndpointCircleKernel
