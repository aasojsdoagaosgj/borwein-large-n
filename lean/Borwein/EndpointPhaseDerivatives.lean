import Borwein.EndpointPhaseSeries

set_option autoImplicit false

namespace Borwein.EndpointPhaseDerivatives
noncomputable section
open Complex EndpointPhaseAtoms EndpointPhaseSeries EndpointSharpTail EndpointTailMain

def q0 (n : ℕ) (v y : ℝ) : ℂ := series n 0 0 v y
def q1 (n : ℕ) (v y : ℝ) : ℂ := -(series n 1 0 v y+series n 0 1 v y)
def q2 (n : ℕ) (v y : ℝ) : ℂ := series n 2 0 v y+2*series n 1 1 v y+2*series n 0 2 v y
def q3 (n : ℕ) (v y : ℝ) : ℂ := -(series n 3 0 v y+3*series n 2 1 v y+6*series n 1 2 v y+6*series n 0 3 v y)
def q4 (n : ℕ) (v y : ℝ) : ℂ := series n 4 0 v y+4*series n 3 1 v y+12*series n 2 2 v y+24*series n 1 3 v y+24*series n 0 4 v y

theorem q0_deriv (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasDerivAt (q0 n v) (I*q1 n v y) y := by
  apply (series_deriv n 0 0 v y hn hv).congr_deriv
  simp only [q1]
  norm_num
  ring

theorem q1_deriv (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasDerivAt (q1 n v) (I*q2 n v y) y := by
  apply ((series_deriv n 1 0 v y hn hv).add (series_deriv n 0 1 v y hn hv)).neg.congr_deriv
  norm_num [q2]
  ring

theorem q2_deriv (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasDerivAt (q2 n v) (I*q3 n v y) y := by
  apply (((series_deriv n 2 0 v y hn hv).add ((series_deriv n 1 1 v y hn hv).const_mul 2)).add
    ((series_deriv n 0 2 v y hn hv).const_mul 2)).congr_deriv
  norm_num [q3]
  ring

theorem q3_deriv (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasDerivAt (q3 n v) (I*q4 n v y) y := by
  apply ((((series_deriv n 3 0 v y hn hv).add ((series_deriv n 2 1 v y hn hv).const_mul 3)).add
    ((series_deriv n 1 2 v y hn hv).const_mul 6)).add
    ((series_deriv n 0 3 v y hn hv).const_mul 6)).neg.congr_deriv
  norm_num [q4]
  ring

theorem q4_continuous (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) : Continuous (q4 n v) :=
  ((((series_continuous n 4 0 v hn hv).add ((series_continuous n 3 1 v hn hv).const_mul 4)).add
    ((series_continuous n 2 2 v hn hv).const_mul 12)).add
    ((series_continuous n 1 3 v hn hv).const_mul 24)).add
    ((series_continuous n 0 4 v hn hv).const_mul 24)

theorem component_lambda (n k : ℕ) (v y : ℝ) :
    component n 0 0 v y k=lambdaTerm (x n (coordinate v y)) (coordinate v y) k := by
  have hx : x n (coordinate v y)^k=exp (-(frequency n k:ℂ)*coordinate v y) := by
    rw [x, ← exp_nat_mul]
    congr 1
    unfold frequency
    push_cast
    ring
  unfold component atom lambdaTerm sparseTerm coefficient
  rw [hx]
  by_cases hk : 5 ∣ k
  · simp only [if_pos hk, pow_zero, mul_one, zero_add, pow_one]
    push_cast
    ring
  · simp only [if_neg hk, pow_zero, mul_one, zero_add, pow_one]
    push_cast
    ring

theorem q0_eq_lambda (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    q0 n v y=lambda (x n (coordinate v y))/(5*coordinate v y) := by
  have hw : 0 < (coordinate v y).re := by simpa only [coordinate_re] using hv
  have hh := lambda_hasSum (x n (coordinate v y)) (coordinate v y) (x_norm_lt_one n _ hn hw).le
  exact (hh.congr_fun (fun k => component_lambda n k v y)).tsum_eq

theorem actual_phase_split (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    (n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*coordinate v y)=
      (2*(Real.pi:ℂ)^2/75)/coordinate v y+q0 n v y := by
  rw [q0_eq_lambda n v y hn hv]
  exact (EndpointFiniteTailExpansion.radial_exponent n _ hn (by simpa only [coordinate_re] using hv)).symm

end
end Borwein.EndpointPhaseDerivatives
