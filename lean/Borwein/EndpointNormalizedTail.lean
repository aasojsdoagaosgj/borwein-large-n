import Borwein.EndpointFiniteTailExpansion

set_option autoImplicit false

namespace Borwein.EndpointNormalizedTail
noncomputable section
open Complex EndpointSharpTail EndpointTailMain EndpointFiniteTailExpansion

def leading (n : ℕ) (j : Fin 4) (w : ℂ) : ℂ :=
  EndpointRootAsymptotic.kappa j * exp ((n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*w)-w/6+
    phase (FivePoleCircle.zeta^(j.val+1)) (x n w))
def budget (n : ℕ) (w : ℂ) : ℝ := 5*‖w‖*‖x n w‖/(1-‖x n w‖)

theorem leading_ne_zero (n : ℕ) (j : Fin 4) (w : ℂ) : leading n j w ≠ 0 :=
  mul_ne_zero (EndpointRootAsymptotic.kappa_ne_zero j) (exp_ne_zero _)

theorem polynomial_ratio (n : ℕ) (j : Fin 4) (w : ℂ)
    (hn : 0 < n) (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    Polynomial.eval₂ (Int.castRingHom ℂ) (FivePoleCircle.zeta^(j.val+1)*exp (-w))
      (Borwein.polynomial n)/leading n j w =
      exp (tailError n (FivePoleCircle.zeta^(j.val+1)) w)*EndpointRootAsymptotic.correction j w := by
  rw [polynomial_expansion n j w hn hw hi, Complex.exp_add]
  rw [← mul_assoc (EndpointRootAsymptotic.kappa j)]
  change (leading n j w*exp (tailError n (FivePoleCircle.zeta^(j.val+1)) w)*
    EndpointRootAsymptotic.correction j w)/leading n j w = _
  rw [mul_assoc, mul_div_cancel_left₀ _ (leading_ne_zero n j w)]

theorem exp_correction_error (E U : ℂ) (C η : ℝ) (hE : ‖E‖ ≤ C) (hU : ‖U-1‖ ≤ η) :
    ‖exp E*U-1‖ ≤ (C+η)*Real.exp C := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hU
  have hC : 0 ≤ C := (norm_nonneg _).trans hE
  have he := (Complex.norm_exp_le_exp_norm E).trans (Real.exp_le_exp.mpr hE)
  have hd : ‖exp E-1‖ ≤ C*Real.exp C := by
    have hb := Complex.norm_exp_sub_sum_le_norm_mul_exp E 1
    simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one] at hb
    exact hb.trans (mul_le_mul hE (Real.exp_le_exp.mpr hE) (Real.exp_pos _).le hC)
  have hm : ‖(U-1)*exp E‖ ≤ η*Real.exp C := by
    rw [norm_mul]
    exact mul_le_mul hU he (norm_nonneg _) hη
  have hi : exp E*U-1 = (U-1)*exp E+(exp E-1) := by ring
  rw [hi]
  exact (norm_add_le _ _).trans (by linarith)

theorem normalized_error (n : ℕ) (j : Fin 4) (v y : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hy : |y| ≤ 3*v/4) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ)
      (FivePoleCircle.zeta^(j.val+1)*exp (-((v:ℂ)+(y:ℂ)*I)))
      (Borwein.polynomial n)/leading n j ((v:ℂ)+(y:ℂ)*I)-1‖ ≤
        (budget n ((v:ℂ)+(y:ℂ)*I)+10*Real.exp (-1/v))*Real.exp (budget n ((v:ℂ)+(y:ℂ)*I)) := by
  have hw : 0 < ((v:ℂ)+(y:ℂ)*I).re := by simpa using hv
  have hi : |((v:ℂ)+(y:ℂ)*I).im| ≤ 3*((v:ℂ)+(y:ℂ)*I).re/4 := by simpa using hy
  rw [polynomial_ratio n j _ hn hw hi]
  apply exp_correction_error
  · exact sharp_error_bound n _ _ (EndpointTailRootSeries.actual_root_fifth j) hn hw hi
  · exact EndpointRootAsymptotic.correction_error j v y hv hV hy

end
end Borwein.EndpointNormalizedTail
