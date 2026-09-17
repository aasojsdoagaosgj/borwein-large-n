import Borwein.EndpointPhaseDerivatives

set_option autoImplicit false

namespace Borwein.EndpointActualPhase
noncomputable section
open Complex EndpointPhaseAtoms EndpointPhaseDerivatives

def A : ℝ := 2*Real.pi^2/75
def f0 (n : ℕ) (v y : ℝ) : ℂ := (A:ℂ)*atom 0 0 v y+q0 n v y
def f1 (n : ℕ) (v y : ℝ) : ℂ := -(A:ℂ)*atom 0 1 v y+q1 n v y
def f2 (n : ℕ) (v y : ℝ) : ℂ := 2*(A:ℂ)*atom 0 2 v y+q2 n v y
def f3 (n : ℕ) (v y : ℝ) : ℂ := -6*(A:ℂ)*atom 0 3 v y+q3 n v y
def f4 (n : ℕ) (v y : ℝ) : ℂ := 24*(A:ℂ)*atom 0 4 v y+q4 n v y

theorem f0_eq_actual (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    f0 n v y=(n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*coordinate v y) := by
  rw [actual_phase_split n v y hn hv]
  simp only [f0, atom, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, zero_add, pow_one]
  unfold A
  push_cast
  ring

theorem f0_deriv (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasDerivAt (f0 n v) (I*f1 n v y) y := by
  apply (((atom_deriv 0 0 v y hv).const_mul (A:ℂ)).add (q0_deriv n v y hn hv)).congr_deriv
  norm_num [f1]
  ring

theorem f1_deriv (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasDerivAt (f1 n v) (I*f2 n v y) y := by
  apply (((atom_deriv 0 1 v y hv).const_mul (-(A:ℂ))).add (q1_deriv n v y hn hv)).congr_deriv
  norm_num [f2]
  ring

theorem f2_deriv (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasDerivAt (f2 n v) (I*f3 n v y) y := by
  apply (((atom_deriv 0 2 v y hv).const_mul (2*(A:ℂ))).add (q2_deriv n v y hn hv)).congr_deriv
  norm_num [f3]
  ring

theorem f3_deriv (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasDerivAt (f3 n v) (I*f4 n v y) y := by
  apply (((atom_deriv 0 3 v y hv).const_mul (-6*(A:ℂ))).add (q3_deriv n v y hn hv)).congr_deriv
  norm_num [f4]
  ring

theorem atom_continuous (c : ℝ) (j : ℕ) (v : ℝ) (hv : 0 < v) : Continuous (atom c j v) :=
  continuous_iff_continuousAt.mpr (fun y => (atom_deriv c j v y hv).continuousAt)

theorem f4_continuous (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) : Continuous (f4 n v) :=
  ((atom_continuous 0 4 v hv).const_mul (24*(A:ℂ))).add (q4_continuous n v hn hv)

end
end Borwein.EndpointActualPhase
