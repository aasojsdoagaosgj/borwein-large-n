import Borwein.EndpointRadialDifferentiation
import Borwein.SaddlePoint
import Borwein.SmallBoxPhaseDecay

set_option autoImplicit false

namespace Borwein.EndpointSaddleIdentification
noncomputable section
open Complex Set Filter EndpointPhaseAtoms EndpointPhaseSeries EndpointPhaseDerivatives
  EndpointActualPhase EndpointRadialDifferentiation RadialDerivatives PhaseIntegral
open scoped Topology

def firstModel (n : ℕ) (v : ℝ) : ℝ := 5*(n:ℝ)^2*firstDerivative (((5*n:ℕ):ℝ)*v)
def secondModel (n : ℕ) (v : ℝ) : ℝ := 25*(n:ℝ)^3*secondDerivative (((5*n:ℕ):ℝ)*v)

theorem radial_q0_deriv (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasDerivAt (fun s => q0 n s 0) (q1 n v 0) v := by
  apply (radial_series_deriv n 0 0 v hn hv).congr_deriv
  norm_num [q1]

theorem radial_q1_deriv (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasDerivAt (fun s => q1 n s 0) (q2 n v 0) v := by
  apply ((radial_series_deriv n 1 0 v hn hv).add (radial_series_deriv n 0 1 v hn hv)).neg.congr_deriv
  norm_num [q2]
  ring

theorem radial_f0_deriv (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasDerivAt (fun s => f0 n s 0) (f1 n v 0) v := by
  apply (((radial_atom_deriv 0 0 v hv).const_mul (A:ℂ)).add (radial_q0_deriv n v hn hv)).congr_deriv
  norm_num [f1]

theorem radial_f1_deriv (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasDerivAt (fun s => f1 n s 0) (f2 n v 0) v := by
  apply (((radial_atom_deriv 0 1 v hv).const_mul (-(A:ℂ))).add (radial_q1_deriv n v hn hv)).congr_deriv
  norm_num [f2]
  ring

theorem radial_f0_value (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    f0 n v 0=(((n:ℝ)*radialR (((5*n:ℕ):ℝ)*v):ℝ):ℂ) := by
  rw [f0_eq_actual n v 0 hn hv]
  simp only [coordinate, Complex.ofReal_zero, zero_mul, add_zero]
  rw [show ((5*n:ℕ):ℂ)*(v:ℂ)=((((5*n:ℕ):ℝ)*v:ℝ):ℂ) by push_cast; rfl,
    SmallBoxPhaseDecay.complexR_real]
  push_cast
  rfl

theorem model_first_deriv (n : ℕ) (v : ℝ) :
    HasDerivAt (fun s => (n:ℝ)*radialR (((5*n:ℕ):ℝ)*s)) (firstModel n v) v := by
  apply (((hasDerivAt_radialR (((5*n:ℕ):ℝ)*v)).comp v
    ((hasDerivAt_id v).const_mul (((5*n:ℕ):ℝ)))).const_mul (n:ℝ)).congr_deriv
  unfold firstModel
  push_cast
  ring

theorem first_identification (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    f1 n v 0=(firstModel n v:ℂ) := by
  have he : (fun s => f0 n s 0) =ᶠ[𝓝 v]
      (fun s => (((n:ℝ)*radialR (((5*n:ℕ):ℝ)*s):ℝ):ℂ)) :=
    (eventually_gt_nhds hv).mono (fun s hs => radial_f0_value n s hn hs)
  exact (radial_f0_deriv n v hn hv).unique
    ((model_first_deriv n v).ofReal_comp.congr_of_eventuallyEq he)

theorem model_second_deriv (n : ℕ) (v : ℝ) : HasDerivAt (firstModel n) (secondModel n v) v := by
  apply (((hasDerivAt_firstDerivative (((5*n:ℕ):ℝ)*v)).comp v
    ((hasDerivAt_id v).const_mul (((5*n:ℕ):ℝ)))).const_mul (5*(n:ℝ)^2)).congr_deriv
  unfold secondModel
  push_cast
  ring

theorem second_identification (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    f2 n v 0=(secondModel n v:ℂ) := by
  have he : (fun s => f1 n s 0) =ᶠ[𝓝 v] (fun s => (firstModel n s:ℂ)) :=
    (eventually_gt_nhds hv).mono (fun s hs => first_identification n s hn hs)
  exact (radial_f1_deriv n v hn hv).unique
    ((model_second_deriv n v).ofReal_comp.congr_of_eventuallyEq he)

theorem quadratic_real (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) : (f2 n v 0).im=0 := by
  rw [second_identification n v hn hv, Complex.ofReal_im]

theorem quadratic_positive (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) : 0 < (f2 n v 0).re := by
  rw [second_identification n v hn hv, Complex.ofReal_re, secondModel]
  exact mul_pos (by positivity) (RadialDerivatives.secondDerivative_pos _)

theorem original_second_derivative (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    f2 n v 0=((25*(n:ℝ)^3*deriv (deriv radialR) (((5*n:ℕ):ℝ)*v)):ℂ) := by
  rw [second_identification n v hn hv, deriv_two_radialR]
  unfold secondModel
  push_cast
  rfl

end
end Borwein.EndpointSaddleIdentification
