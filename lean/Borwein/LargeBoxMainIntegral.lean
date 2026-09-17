import Borwein.LargeBoxEulerMaclaurin

namespace Borwein.LargeBoxMainIntegral
noncomputable section
open Complex Set MeasureTheory LogFactorDerivatives FiveRootProductExpansion FifthRootLogarithm PhaseIntegral

theorem coefficient_log_continuous (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 6/5) (j : Fin 4) :
    ContinuousOn (f0 (coefficients ξ j) z) (Icc (0:ℝ) 1) := by
  apply ContinuousOn.clog
  · unfold kernel w; fun_prop
  · exact uniform_slit _ z (coefficients_norm ξ (root_norm ξ hξ.pow_eq_one).le j) hz (1/20)
      (by norm_num) (LargeBoxSeparation.coefficient_gap ξ z hξ hi j)

theorem rootLog_continuous (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 6/5) : ContinuousOn (rootLog ξ z) (Icc (0:ℝ) 1) := by
  unfold rootLog
  exact continuousOn_finsetSum _ (fun j _ => coefficient_log_continuous ξ z hξ hz hi j)

theorem exp_rootLog (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5) (hi : |z.im| ≤ 6/5)
    (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : Complex.exp (rootLog ξ z x) = fiveSum (z*(x:ℂ)) := by
  rw [rootLog,Complex.exp_sum,← factor_product ξ z hξ x]
  apply Finset.prod_congr rfl
  intro j _
  exact Complex.exp_log (norm_pos_iff.mp ((by norm_num : (0:ℝ) < 1/20).trans_le
    (LargeBoxSeparation.coefficient_gap ξ z hξ hi j x hx)))

theorem rootLog_real_part (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5) (hi : |z.im| ≤ 6/5)
    (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : (rootLog ξ z x).re = Real.log ‖fiveSum (z*(x:ℂ))‖ := by
  rw [← exp_rootLog ξ z hξ hi x hx,Complex.norm_exp,Real.log_exp]

theorem rootIntegral_real_part (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 6/5) : (rootIntegral ξ z).re = (complexR z).re := by
  have hc := rootLog_continuous ξ z hξ hz hi
  have hr : rootIntegral ξ z = ∫ x in (0:ℝ)..1, rootLog ξ z x := by
    unfold rootIntegral rootLog
    rw [intervalIntegral.integral_finsetSum]
    intro j _
    exact (coefficient_log_continuous ξ z hξ hz hi j).intervalIntegrable_of_Icc (by norm_num)
  have hfn : ∀ x ∈ Icc (0:ℝ) 1, fiveSum (z*(x:ℂ)) ≠ 0 := by
    intro x hx
    rw [← exp_rootLog ξ z hξ hi x hx]
    exact Complex.exp_ne_zero _
  have hfc : Continuous (fun x : ℝ => fiveSum (z*(x:ℂ))) := by unfold fiveSum; fun_prop
  have hlog := hfc.norm.continuousOn.log (fun x hx => norm_ne_zero_iff.mpr (hfn x hx))
  have hic := intervalIntegrable_clog _ 0 1 (by norm_num) hfc hlog
  have hrre : (∫ x in (0:ℝ)..1, rootLog ξ z x).re = ∫ x in (0:ℝ)..1, (rootLog ξ z x).re := by
    exact (intervalIntegral.intervalIntegral_re (hc.intervalIntegrable_of_Icc (μ := volume) (by norm_num))).symm
  have hcre : (∫ x in (0:ℝ)..1, Complex.log (fiveSum (z*(x:ℂ)))).re =
      ∫ x in (0:ℝ)..1, (Complex.log (fiveSum (z*(x:ℂ)))).re := by
    exact (intervalIntegral.intervalIntegral_re hic).symm
  rw [hr,complexR,hrre,hcre]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [Complex.log_re]
  exact rootLog_real_part ξ z hξ hi x (by simpa using hx)

end
end Borwein.LargeBoxMainIntegral
