import Borwein.EndpointPhaseDecay

set_option autoImplicit false

namespace Borwein.EndpointSaddleEnergy
noncomputable section
open Complex EndpointPhaseAtoms EndpointActualPhase EndpointSaddleIdentification
  EndpointTaylor EndpointPhaseDecay RadialDerivatives PhaseIntegral

def energy (n : ℕ) (k v y : ℝ) : ℂ := f0 n v y+(k:ℂ)*coordinate v y

theorem actual_energy (n : ℕ) (k v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    energy n k v y=(n:ℂ)*complexR (((5*n:ℕ):ℂ)*coordinate v y)+(k:ℂ)*coordinate v y := by
  rw [energy, f0_eq_actual n v y hn hv]

theorem energy_deriv (n : ℕ) (k v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasDerivAt (energy n k v) (I*(f1 n v y+(k:ℂ))) y := by
  apply ((f0_deriv n v y hn hv).add ((coordinate_deriv v y).const_mul (k:ℂ))).congr_deriv
  ring

theorem saddle_equation (n : ℕ) (k v : ℝ) (hn : 0 < n)
    (hs : -deriv radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) : firstModel n v+k=0 := by
  rw [deriv_radialR] at hs
  have hh := (eq_div_iff (by positivity : (5*(n:ℝ)^2) ≠ 0)).mp hs
  unfold firstModel
  nlinarith

theorem energy_stationary (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hs : -deriv radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    HasDerivAt (energy n k v) 0 0 := by
  apply (energy_deriv n k v 0 hn hv).congr_deriv
  rw [first_identification n v hn hv, ← Complex.ofReal_add, saddle_equation n k v hn hs]
  simp

theorem energy_difference (n : ℕ) (k v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hs : -deriv radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    energy n k v y-energy n k v 0=phase n v y := by
  have hh : (firstModel n v:ℂ)+(k:ℂ)=0 := by
    rw [← Complex.ofReal_add, saddle_equation n k v hn hs, Complex.ofReal_zero]
  unfold energy phase coordinate
  rw [first_identification n v hn hv]
  push_cast
  linear_combination I*(y:ℂ)*hh

theorem energy_zero (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    energy n k v 0=(((n:ℝ)*radialR (((5*n:ℕ):ℝ)*v)+k*v:ℝ):ℂ) := by
  rw [energy, radial_f0_value n v hn hv]
  simp [coordinate]

theorem energy_decay (n : ℕ) (k v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hs : -deriv radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2))
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hy : |y| ≤ 3*v/4) :
    (energy n k v y-energy n k v 0).re ≤ -(97/1000)*(y^2/v^3) := by
  rw [energy_difference n k v y hn hv hs]
  exact phase_decay n v y hn hv hτ hy

theorem energy_exponential_remainder (n : ℕ) (k v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hs : -deriv radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2))
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hy : |y| ≤ 3*v/4) :
    ‖exp (energy n k v y-energy n k v 0)-exp (gaussian n v y)‖ ≤
      ((64/25)*|y|^3/(6*v^4))*Real.exp (-(97/1000)*(y^2/v^3)) := by
  rw [energy_difference n k v y hn hv hs]
  exact exponential_remainder n v y hn hv hτ hy

end
end Borwein.EndpointSaddleEnergy
