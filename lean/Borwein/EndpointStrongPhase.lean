import Borwein.EndpointStrongConstants
import Borwein.EndpointCombinedTail

set_option autoImplicit false

namespace Borwein.EndpointStrongPhase
noncomputable section
open Complex FivePoleCircle EndpointRootCancellation EndpointRootLinear EndpointCombinedPhase
open EndpointTailMain EndpointRootPhaseSeries EndpointSharpTail EndpointCombinedTail EndpointStrongConstants

theorem linear_bound (a : ℕ) : ‖linear a‖ ≤ 4 := by
  unfold linear
  apply (norm_sum_le _ _).trans
  have h : ∑ j : Fin 4, ‖weight a j*(zeta^(j.val+1)/(1-zeta^(j.val+1))+1/2)‖ ≤ ∑ _j : Fin 4, (1:ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul, weight_norm, one_mul]
    have hb := coefficient_bound (zeta^(j.val+1)) (actual_root_primitive j) 1
    rw [first_coefficient] at hb
    simpa using hb
  simpa using h

theorem phase_difference (a : ℕ) (x : ℂ) (hx : ‖x‖ ≤ 1/10) :
    ‖combined a x-constant a‖ ≤ 8*‖x‖ := by
  have h1 := combined_remainder a x hx
  have h2 : ‖linear a*x‖ ≤ 4*‖x‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (linear_bound a) (norm_nonneg x)
  have he : combined a x-constant a = (combined a x-constant a-linear a*x)+linear a*x := by ring
  rw [he]
  have h := norm_add_le (combined a x-constant a-linear a*x) (linear a*x)
  have hr := mul_nonneg (norm_nonneg x) (sub_nonneg.mpr hx)
  nlinarith

theorem phase_relative_error (a : Fin 3) (x : ℂ) (hx : ‖x‖ ≤ 1/10) :
    ‖combined a.val x/constant a.val-1‖ ≤ 8*‖x‖ := by
  have hc := constant_ne_zero a
  have he : combined a.val x/constant a.val-1 = (combined a.val x-constant a.val)/constant a.val := by field_simp
  rw [he, norm_div]
  exact (div_le_self (norm_nonneg _) (constant_norm_lower a)).trans (phase_difference a.val x hx)

theorem perturbed_relative_error (a : Fin 3) (n : ℕ) (w : ℂ) (hn : 0 < n)
    (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4)
    (hr : ‖x n w‖ ≤ 1/100) (hwn : ‖w‖ ≤ 1/100) :
    ‖perturbed a.val n w/constant a.val-1‖ ≤ 8*‖x n w‖+25*‖w‖ := by
  have hc := constant_ne_zero a
  have he : perturbed a.val n w/constant a.val-1 = (perturbed a.val n w-constant a.val)/constant a.val := by field_simp
  rw [he, norm_div]
  apply (div_le_self (norm_nonneg _) (constant_norm_lower a)).trans
  have h1 := perturbed_difference a.val n w hn hw hi hr hwn
  have h2 := phase_difference a.val (x n w) (by linarith)
  have hid : perturbed a.val n w-constant a.val =
      (perturbed a.val n w-combined a.val (x n w))+(combined a.val (x n w)-constant a.val) := by ring
  rw [hid]
  have h := norm_add_le (perturbed a.val n w-combined a.val (x n w)) (combined a.val (x n w)-constant a.val)
  have hp := mul_nonneg (norm_nonneg w) (show 0 ≤ 1-‖x n w‖ by linarith)
  nlinarith

end
end Borwein.EndpointStrongPhase
