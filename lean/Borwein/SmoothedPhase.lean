import Borwein.PhaseSingular

namespace Borwein.SmoothedPhase
noncomputable section
open scoped BigOperators
open Borwein.PhaseGap Borwein.PhaseIntegral Borwein.PhaseSingular

def smoothedPhase (η τ t x : ℝ) : ℂ :=
  amplitude (radialWeight (η+τ*x)) (fun j => (j:ℝ)*(t*x))
def smoothedGap (η τ t x : ℝ) := groupedGap (radialWeight (η+τ*x)) (t*x)
def smoothedSum (η τ t x : ℝ) : ℂ :=
  fiveSum (((η+τ*x:ℝ):ℂ)-((t*x:ℝ):ℂ)*Complex.I)

theorem smoothedPhase_formula (η τ t x : ℝ) :
    smoothedPhase η τ t x = smoothedSum η τ t x / (radialSum (η+τ*x):ℂ) := by
  simpa [smoothedPhase, smoothedSum, phase] using phase_eq_fiveSum_div (η+τ*x) (t*x) 1

theorem continuous_smoothedPhase (η τ t : ℝ) : Continuous (smoothedPhase η τ t) := by
  have hp (j : Fin 5) : Continuous (fun x : ℝ => radialWeight (η+τ*x) j) := by fun_prop
  unfold smoothedPhase
  simp_rw [amplitude_eq_exp_sum]
  fun_prop

theorem continuous_smoothedGap (η τ t : ℝ) : Continuous (smoothedGap η τ t) := by
  have hp (j : Fin 5) : Continuous (fun x : ℝ => radialWeight (η+τ*x) j) := by fun_prop
  unfold smoothedGap groupedGap
  fun_prop

theorem smoothedPhase_ne_zero (η τ t x : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hx : 0 ≤ x) :
    smoothedPhase η τ t x ≠ 0 :=
  radial_amplitude_ne_zero _ _ (lt_of_lt_of_le hη (le_add_of_nonneg_right (mul_nonneg hτ hx)))

theorem integral_smoothed_gap_pos (η τ t : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) :
    (∫ x in (0:ℝ)..1, smoothedGap η τ t x + smoothedGap η τ t x^2) ≤
      ∫ x in (0:ℝ)..1, -Real.log ‖smoothedPhase η τ t x‖ := by
  apply integral_norm_log_quadratic _ _ 0 1 (by norm_num)
    (continuous_smoothedPhase η τ t).continuousOn (continuous_smoothedGap η τ t).continuousOn
  · intro x _
    simpa [smoothedGap, pairGap_eq_groupedGap] using
      pairGap_nonneg (radialWeight (η+τ*x)) (fun j => (j:ℝ)*(t*x))
        (fun j => (radialWeight_pos (η+τ*x) j).le)
  · intro x hx
    exact smoothedPhase_ne_zero η τ t x hη hτ hx.1
  · intro x _
    simpa [smoothedPhase, smoothedGap, pairGap_eq_groupedGap] using
      amplitude_norm_sq (radialWeight (η+τ*x)) (fun j => (j:ℝ)*(t*x)) (radialWeight_sum _)

theorem integral_smoothed_gap (η τ t : ℝ) (hη : 0 ≤ η) (hτ : 0 ≤ τ) :
    (∫ x in (0:ℝ)..1, smoothedGap η τ t x + smoothedGap η τ t x^2) ≤
      ∫ x in (0:ℝ)..1, -Real.log ‖smoothedPhase η τ t x‖ := by
  obtain rfl | hη := hη.eq_or_lt
  · simpa [smoothedGap, smoothedPhase, gapDensity, phase] using integral_phase_gap_nonneg τ t hτ
  · exact integral_smoothed_gap_pos η τ t hη hτ

theorem radialSum_shift_le (η y : ℝ) (hη : 0 ≤ η) : radialSum (η+y) ≤ radialSum y := by
  apply Finset.sum_le_sum
  intro j _
  apply Real.exp_le_exp.mpr
  have hj : 0 ≤ (j:ℝ) := by positivity
  nlinarith [mul_nonneg hj hη]

theorem log_radialSum_shift_le (η y : ℝ) (hη : 0 ≤ η) :
    Real.log (radialSum (η+y)) ≤ Real.log (radialSum y) :=
  Real.log_le_log (radialDenominator_pos _) (radialSum_shift_le η y hη)

def smoothedModulus (η τ t : ℝ) := ∫ x in (0:ℝ)..1, Real.log ‖smoothedSum η τ t x‖
def smoothedRadial (η τ : ℝ) := ∫ x in (0:ℝ)..1, Real.log (radialSum (η+τ*x))

theorem continuous_log_shifted (η τ : ℝ) :
    Continuous (fun x : ℝ => Real.log (radialSum (η+τ*x))) := by
  apply Continuous.log (continuous_radialSum.comp (by fun_prop))
  intro x
  exact ne_of_gt (radialDenominator_pos _)

theorem smoothedRadial_le (η τ : ℝ) (hη : 0 ≤ η) : smoothedRadial η τ ≤ radialR τ := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_log_shifted η τ).intervalIntegrable _ _)
    ((continuous_log_radialSum τ).intervalIntegrable _ _)
  intro x _
  exact log_radialSum_shift_le η (τ*x) hη

theorem integral_smoothed_normalization_pos (η τ t : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) :
    (∫ x in (0:ℝ)..1, -Real.log ‖smoothedPhase η τ t x‖) =
      smoothedRadial η τ-smoothedModulus η τ t := by
  have hn (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) : smoothedSum η τ t x ≠ 0 := by
    intro hz
    have h := smoothedPhase_ne_zero η τ t x hη hτ hx.1
    rw [smoothedPhase_formula, hz, zero_div] at h
    exact h rfl
  have hc : Continuous (smoothedSum η τ t) := continuous_fiveSum.comp (by fun_prop)
  have hl := hc.norm.continuousOn.log (fun x hx => norm_ne_zero_iff.mpr (hn x hx))
  calc
    _ = ∫ x in (0:ℝ)..1, Real.log (radialSum (η+τ*x))-Real.log ‖smoothedSum η τ t x‖ := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxi : x ∈ Set.Icc (0:ℝ) 1 := by simpa using hx
      change -Real.log ‖smoothedPhase η τ t x‖ =
        Real.log (radialSum (η+τ*x))-Real.log ‖smoothedSum η τ t x‖
      rw [smoothedPhase_formula, norm_div, Complex.norm_real,
        Real.norm_of_nonneg (show 0 ≤ radialSum (η+τ*x) from (radialDenominator_pos _).le),
        Real.log_div (norm_ne_zero_iff.mpr (hn x hxi))
          (show radialSum (η+τ*x) ≠ 0 from ne_of_gt (radialDenominator_pos _))]
      ring
    _ = _ := intervalIntegral.integral_sub
      ((continuous_log_shifted η τ).intervalIntegrable _ _)
      (hl.intervalIntegrable_of_Icc (by norm_num))

theorem integral_smoothed_normalization (η τ t : ℝ) (hη : 0 ≤ η) (hτ : 0 ≤ τ) :
    (∫ x in (0:ℝ)..1, -Real.log ‖smoothedPhase η τ t x‖) =
      smoothedRadial η τ-smoothedModulus η τ t := by
  obtain rfl | hη := hη.eq_or_lt
  · have hp : smoothedPhase 0 τ t = phase τ t := by
      funext x
      simp [smoothedPhase, phase]
    have hr : smoothedRadial 0 τ = radialR τ := by simp [smoothedRadial, radialR]
    rw [hp, hr, integral_phase_R_nonneg τ t hτ, ← modulusR_eq_re_complexR_all]
    congr 1
    apply intervalIntegral.integral_congr
    intro x _
    change Real.log ‖fiveSum (((τ:ℂ)-(t:ℂ)*Complex.I)*(x:ℂ))‖ =
      Real.log ‖fiveSum (((0+τ*x:ℝ):ℂ)-((t*x:ℝ):ℂ)*Complex.I)‖
    congr 3
    push_cast
    ring
  · exact integral_smoothed_normalization_pos η τ t hη hτ

theorem smoothedModulus_upper (η τ t : ℝ) (hη : 0 ≤ η) (hτ : 0 ≤ τ) :
    smoothedModulus η τ t ≤ radialR τ -
      ∫ x in (0:ℝ)..1, smoothedGap η τ t x+smoothedGap η τ t x^2 := by
  have h := integral_smoothed_gap η τ t hη hτ
  rw [integral_smoothed_normalization η τ t hη hτ] at h
  have hr := smoothedRadial_le η τ hη
  linarith

end
end Borwein.SmoothedPhase
