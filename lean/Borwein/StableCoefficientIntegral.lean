import Borwein.StableBorweinSeries
import Borwein.BorweinTailConvergence
import Borwein.EndpointOuterTransfer
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

namespace Borwein.StableCoefficientIntegral
noncomputable section
open Complex MeasureTheory Set Filter EndpointCircleKernel EndpointCircleFunctions
  BorweinTailConvergence StableBorweinSeries
open scoped Topology

theorem integral_error_bound (m : ℕ) (v : ℝ) (hv : 0 < v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖((Borwein.polynomial n).coeff m:ℂ)*(2*Real.pi:ℂ)-GIntegral m v‖ ≤
        C*((Real.exp (-v))^5)^n := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((G_continuous v hv).continuousOn (s := Icc (0:ℝ) (2*Real.pi)))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, by positivity⟩)
  let r := Real.exp (-v)
  let D := logBudget r
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hD : 0 ≤ D := logBudget_nonneg r hr0
  refine ⟨(2*Real.pi)*(M*(D*Real.exp D)*Real.exp ((m:ℝ)*v)), by positivity, ?_⟩
  intro n
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 2*Real.pi) (f := kernel (difference n) m v)
    (C := (M*(D*Real.exp D)*Real.exp ((m:ℝ)*v))*(r^5)^n) (by
      intro t ht
      rw [uIoc_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)] at ht
      have hq : ‖point v t‖ < 1 := by rw [point_norm]; exact hr1
      have hb := polynomial_difference_bound n (point v t) hq
      rw [point_norm] at hb
      have hG := hM t ⟨ht.1.le, ht.2⟩
      rw [EndpointOuterTransfer.kernel_norm]
      calc
        _ ≤ (‖EndpointEta.G (point v t)‖*(D*Real.exp D)*(r^5)^n)*Real.exp ((m:ℝ)*v) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        _ ≤ (M*(D*Real.exp D)*(r^5)^n)*Real.exp ((m:ℝ)*v) := by gcongr
        _ = _ := by ring)
  rw [difference_integral n m v hv] at hi
  apply hi.trans_eq
  rw [sub_zero, abs_of_pos (by positivity : (0:ℝ)<2*Real.pi)]
  dsimp [r]
  ring

theorem coefficient_integral_limit (m : ℕ) (v : ℝ) (hv : 0 < v) :
    Tendsto (fun n : ℕ => ((Borwein.polynomial n).coeff m:ℂ)*(2*Real.pi:ℂ))
      atTop (𝓝 (GIntegral m v)) := by
  obtain ⟨C,hC,hb⟩ := integral_error_bound m v hv
  have hr0 : 0 ≤ (Real.exp (-v))^5 := by positivity
  have hr1 : (Real.exp (-v))^5 < 1 := pow_lt_one₀ (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by linarith)) (by norm_num)
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul C
  rw [mul_zero] at ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) hb ht

theorem stable_integral (m : ℕ) (v : ℝ) (hv : 0 < v) :
    (stableCoeff m:ℂ)*(2*Real.pi:ℂ) = GIntegral m v := by
  have hc : Tendsto (fun n : ℕ => ((Borwein.polynomial n).coeff m:ℂ)*(2*Real.pi:ℂ))
      atTop (𝓝 ((stableCoeff m:ℂ)*(2*Real.pi:ℂ))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (m+1)] with n hn
    rw [stableCoeff_eq n m (by omega)]
  exact tendsto_nhds_unique hc (coefficient_integral_limit m v hv)

theorem finite_integral (n m : ℕ) (hm : m ≤ 5*n) (v : ℝ) (hv : 0 < v) :
    ((Borwein.polynomial n).coeff m:ℂ)*(2*Real.pi:ℂ) = GIntegral m v := by
  rw [← stableCoeff_eq n m hm]
  exact stable_integral m v hv

end
end Borwein.StableCoefficientIntegral
