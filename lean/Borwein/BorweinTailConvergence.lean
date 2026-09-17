import Borwein.EndpointTailGlobalLog
import Borwein.EndpointCircleFunctions

set_option autoImplicit false

namespace Borwein.BorweinTailConvergence
noncomputable section
open Complex EndpointTailLog EndpointTailGlobalLog EndpointFiniteConnection

def logBudget (r : ℝ) : ℝ := r/(1-r)^2+r^5/(1-r^5)^2

theorem logBudget_nonneg (r : ℝ) (hr : 0 ≤ r) : 0 ≤ logBudget r := by
  unfold logBudget
  positivity

theorem geometric_log_bound (n : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    ‖tailLog n q‖ ≤ logBudget ‖q‖*(‖q‖^5)^n := by
  have hq5 : ‖q^5‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  calc
    _ ≤ ‖inverseLog (5*n) q‖+‖inverseLog n (q^5)‖ := norm_sub_le _ _
    _ ≤ ‖q‖^(5*n+1)/(1-‖q‖)^2+‖q^5‖^(n+1)/(1-‖q^5‖)^2 :=
      add_le_add (inverseLog_bound _ q hq) (inverseLog_bound _ (q^5) hq5)
    _ = _ := by
      rw [Complex.norm_pow]
      simp only [logBudget, pow_succ, pow_mul]
      ring

theorem geometric_tail_bound (n : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    ‖tail n q-1‖ ≤ (logBudget ‖q‖*Real.exp (logBudget ‖q‖))*(‖q‖^5)^n := by
  have hD := logBudget_nonneg ‖q‖ (norm_nonneg q)
  have hp : (‖q‖^5)^n ≤ 1 := pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) hq.le)
  have hB : logBudget ‖q‖*(‖q‖^5)^n ≤ logBudget ‖q‖ := mul_le_of_le_one_right hD hp
  rw [← exp_tailLog n q hq]
  calc
    _ ≤ (logBudget ‖q‖*(‖q‖^5)^n)*Real.exp (logBudget ‖q‖*(‖q‖^5)^n) :=
      exp_error_bound _ _ (geometric_log_bound n q hq)
    _ ≤ (logBudget ‖q‖*(‖q‖^5)^n)*Real.exp (logBudget ‖q‖) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hB) (by positivity)
    _ = _ := by ring

theorem polynomial_difference_bound (n : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    ‖EndpointCircleFunctions.difference n q‖ ≤
      ‖EndpointEta.G q‖*(logBudget ‖q‖*Real.exp (logBudget ‖q‖))*(‖q‖^5)^n := by
  have he : EndpointCircleFunctions.difference n q = EndpointEta.G q*(tail n q-1) := by
    unfold EndpointCircleFunctions.difference EndpointCircleFunctions.polynomial
    rw [polynomial_eq_G_tail n q hq]
    ring
  rw [he, norm_mul]
  exact (mul_le_mul_of_nonneg_left (geometric_tail_bound n q hq) (norm_nonneg _)).trans_eq (by ring)

end
end Borwein.BorweinTailConvergence
