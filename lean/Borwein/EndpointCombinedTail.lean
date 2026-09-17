import Borwein.EndpointCombinedPhase

set_option autoImplicit false

namespace Borwein.EndpointCombinedTail
noncomputable section
open Complex FivePoleCircle EndpointTailMain EndpointSharpTail EndpointFiniteTailExpansion
open EndpointNormalizedTail EndpointRootCancellation EndpointRootLinear EndpointCombinedPhase EndpointRootPhaseSeries

def perturbed (a n : ℕ) (w : ℂ) : ℂ := ∑ j : Fin 4, weight a j*
  exp (phase (zeta^(j.val+1)) (x n w)+tailError n (zeta^(j.val+1)) w)

theorem phase_exp_bound (ξ x : ℂ) (hξ : IsPrimitiveRoot ξ 5) (hx : ‖x‖ ≤ 1/100) :
    ‖exp (phase ξ x)‖ ≤ 11/10 := by
  have hx1 : ‖x‖ < 1 := by linarith
  have hb := phase_bound ξ x hξ hx1
  have hs : ‖phase ξ x‖ ≤ 1/20 := hb.trans ((div_le_iff₀ (by linarith : 0 < 1-‖x‖)).mpr (by linarith))
  have he := Complex.norm_exp_sub_one_le (x := phase ξ x) (by linarith)
  have ht := norm_add_le (exp (phase ξ x)-1) (1:ℂ)
  simp only [sub_add_cancel, norm_one] at ht
  linarith

theorem budget_bound (n : ℕ) (w : ℂ) (hr : ‖x n w‖ ≤ 1/100) :
    budget n w ≤ (51/10)*‖w‖*‖x n w‖ := by
  have hd : 0 < 1-‖x n w‖ := by linarith
  have he : (5:ℝ)/(1-‖x n w‖) ≤ 51/10 := (div_le_iff₀ hd).mpr (by linarith)
  have hb := mul_le_mul_of_nonneg_right he (mul_nonneg (norm_nonneg w) (norm_nonneg (x n w)))
  calc
    budget n w = (5/(1-‖x n w‖))*(‖w‖*‖x n w‖) := by unfold budget; ring
    _ ≤ (51/10)*‖w‖*‖x n w‖ := by simpa only [mul_assoc] using hb

theorem budget_small (n : ℕ) (w : ℂ) (hr : ‖x n w‖ ≤ 1/100) (hw : ‖w‖ ≤ 1/100) :
    budget n w ≤ 1/10 := by
  have hb := budget_bound n w hr
  have hm := mul_le_mul hw hr (norm_nonneg (x n w)) (by norm_num : (0:ℝ) ≤ 1/100)
  nlinarith

theorem tail_exp_error (n : ℕ) (j : Fin 4) (w : ℂ) (hn : 0 < n)
    (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4)
    (hr : ‖x n w‖ ≤ 1/100) (hwn : ‖w‖ ≤ 1/100) :
    ‖exp (tailError n (zeta^(j.val+1)) w)-1‖ ≤ (11/10)*budget n w := by
  have hb : ‖tailError n (zeta^(j.val+1)) w‖ ≤ budget n w :=
    sharp_error_bound n _ w (EndpointTailRootSeries.actual_root_fifth j) hn hw hi
  have hs : ‖tailError n (zeta^(j.val+1)) w‖ ≤ 1/10 := hb.trans (budget_small n w hr hwn)
  have he := Complex.norm_exp_sub_one_sub_id_le (x := tailError n (zeta^(j.val+1)) w) (by linarith)
  have ht := norm_add_le (exp (tailError n (zeta^(j.val+1)) w)-1-tailError n (zeta^(j.val+1)) w)
    (tailError n (zeta^(j.val+1)) w)
  rw [sub_add_cancel] at ht
  have hm := mul_nonneg (norm_nonneg (tailError n (zeta^(j.val+1)) w)) (sub_nonneg.mpr hs)
  nlinarith

theorem perturbed_difference (a n : ℕ) (w : ℂ) (hn : 0 < n)
    (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4)
    (hr : ‖x n w‖ ≤ 1/100) (hwn : ‖w‖ ≤ 1/100) :
    ‖perturbed a n w-combined a (x n w)‖ ≤ 25*‖w‖*‖x n w‖ := by
  have he : perturbed a n w-combined a (x n w) = ∑ j : Fin 4,
      weight a j*exp (phase (zeta^(j.val+1)) (x n w))*(exp (tailError n (zeta^(j.val+1)) w)-1) := by
    simp only [perturbed, combined, ← Finset.sum_sub_distrib, exp_add]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  have hb : ∑ j : Fin 4, ‖weight a j*exp (phase (zeta^(j.val+1)) (x n w))*(exp (tailError n (zeta^(j.val+1)) w)-1)‖ ≤
      ∑ _j : Fin 4, (11/10)*((11/10)*budget n w) := by
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul, norm_mul, weight_norm, one_mul]
    exact mul_le_mul (phase_exp_bound _ _ (actual_root_primitive j) hr)
      (tail_exp_error n j w hn hw hi hr hwn) (norm_nonneg _) (by norm_num)
  have hsum : (∑ _j : Fin 4, (11/10:ℝ)*((11/10)*budget n w)) = (121/25)*budget n w := by simp; ring
  rw [hsum] at hb
  have hbudget := budget_bound n w hr
  have hp := mul_nonneg (norm_nonneg w) (norm_nonneg (x n w))
  exact hb.trans (by nlinarith)

theorem weak_perturbed_remainder (a n : ℕ) (ha : a=3 ∨ a=4) (w : ℂ) (hn : 0 < n)
    (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4)
    (hr : ‖x n w‖ ≤ 1/100) (hwn : ‖w‖ ≤ 1/100) :
    ‖perturbed a n w+x n w‖ ≤ (8*‖x n w‖+25*‖w‖)*‖x n w‖ := by
  have h1 := perturbed_difference a n w hn hw hi hr hwn
  have h2 := weak_combined_remainder a ha (x n w) (by linarith)
  have he : perturbed a n w+x n w =
      (perturbed a n w-combined a (x n w))+(combined a (x n w)+x n w) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (by nlinarith)

end
end Borwein.EndpointCombinedTail
