import Borwein.ResonantCertificate
import Mathlib.Analysis.Analytic.Order

namespace Borwein.PhaseSingular
noncomputable section
open scoped BigOperators
open Borwein.PhaseGap Borwein.PhaseIntegral Borwein.LogKernel MeasureTheory Filter

theorem phase_zero_formula (t x : ℝ) :
    phase 0 t x = fiveSum (-(t:ℂ)*Complex.I*(x:ℂ))/5 := by
  simp [phase_eq_fiveSum_div, radialSum]

theorem analyticAt_phase_zero (t x : ℝ) : AnalyticAt ℝ (phase 0 t) x := by
  have ha : AnalyticAt ℂ (fun w : ℂ => fiveSum (-(t:ℂ)*Complex.I*w)/5) (x:ℂ) := by
    unfold fiveSum
    fun_prop
  have h := ha.restrictScalars.comp (Complex.ofRealCLM.analyticAt x)
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, ← phase_zero_formula] using h

theorem phase_at_zero (τ t : ℝ) : phase τ t 0 = 1 := by
  simp [phase_eq_fiveSum_div, fiveSum, radialSum]

theorem phase_zero_ae_ne (t : ℝ) : ∀ᵐ x : ℝ, phase 0 t x ≠ 0 := by
  have ha : AnalyticOnNhd ℝ (phase 0 t) Set.univ := fun x _ => analyticAt_phase_zero t x
  have hz := ha.preimage_zero_mem_codiscrete (x := 0) (by rw [phase_at_zero]; norm_num)
  have hh := ae_restrict_le_codiscreteWithin (μ := volume) MeasurableSet.univ hz
  have hh' : ∀ᵐ x ∂volume.restrict Set.univ, x ∈ (phase 0 t) ⁻¹' {0}ᶜ := hh
  simpa only [Measure.restrict_univ, Set.mem_preimage, Set.mem_compl_iff,
    Set.mem_singleton_iff] using hh'

theorem intervalIntegrable_log_phase_zero (t a b : ℝ) :
    IntervalIntegrable (fun x => Real.log ‖phase 0 t x‖) volume a b := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro x _
  exact (analyticAt_phase_zero t x).meromorphicAt

theorem integral_phase_gap_zero_all (t : ℝ) :
    (∫ x in (0:ℝ)..1, gapDensity 0 t x + gapDensity 0 t x^2) ≤
      ∫ x in (0:ℝ)..1, -Real.log ‖phase 0 t x‖ := by
  have hc := continuous_gapDensity 0 t
  apply intervalIntegral.integral_mono_ae (by norm_num)
    ((hc.add (hc.pow 2)).intervalIntegrable _ _)
    (intervalIntegrable_log_phase_zero t 0 1).neg
  filter_upwards [phase_zero_ae_ne t] with x hx
  exact radial_log_gap (0*x) (t*x) hx

theorem integral_phase_gap_nonneg (τ t : ℝ) (hτ : 0 ≤ τ) :
    (∫ x in (0:ℝ)..1, gapDensity τ t x + gapDensity τ t x^2) ≤
      ∫ x in (0:ℝ)..1, -Real.log ‖phase τ t x‖ := by
  obtain rfl | hτ := hτ.eq_or_lt
  · exact integral_phase_gap_zero_all t
  · exact integral_phase_gap τ t hτ


theorem analyticAt_fiveSum_line (z : ℂ) (x : ℝ) :
    AnalyticAt ℝ (fun y : ℝ => fiveSum (z*(y:ℂ))) x := by
  have ha : AnalyticAt ℂ (fun w : ℂ => fiveSum (z*w)) (x:ℂ) := by
    unfold fiveSum
    fun_prop
  exact ha.restrictScalars.comp (Complex.ofRealCLM.analyticAt x)

theorem intervalIntegrable_log_fiveSum_line (z : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log ‖fiveSum (z*(x:ℂ))‖) volume a b := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro x _
  exact (analyticAt_fiveSum_line z x).meromorphicAt

theorem modulusR_eq_re_complexR_all (z : ℂ) : modulusR z = (complexR z).re := by
  have hi := intervalIntegrable_clog_of_log_norm (fun x : ℝ => fiveSum (z*(x:ℂ))) 0 1
    (continuous_fiveSum.comp (by fun_prop)) (intervalIntegrable_log_fiveSum_line z 0 1)
  simpa [modulusR, complexR, Complex.log_re] using
    (intervalIntegral.intervalIntegral_re hi)

theorem integral_phase_zero_R (t : ℝ) :
    (∫ x in (0:ℝ)..1, -Real.log ‖phase 0 t x‖) =
      radialR 0 - (complexR (-(t:ℂ)*Complex.I)).re := by
  rw [← modulusR_eq_re_complexR_all, radialR_zero]
  have he : (∫ x in (0:ℝ)..1, -Real.log ‖phase 0 t x‖) =
      ∫ x in (0:ℝ)..1, Real.log 5-Real.log ‖fiveSum (-(t:ℂ)*Complex.I*(x:ℂ))‖ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [phase_zero_ae_ne t] with x hx
    intro _
    have hn : fiveSum (-(t:ℂ)*Complex.I*(x:ℂ)) ≠ 0 := by
      intro h
      apply hx
      rw [phase_zero_formula, h, zero_div]
    rw [phase_zero_formula, norm_div, Real.log_div (norm_ne_zero_iff.mpr hn) (by norm_num)]
    norm_num
  rw [he, intervalIntegral.integral_sub intervalIntegrable_const
    (intervalIntegrable_log_fiveSum_line _ 0 1)]
  simp [modulusR]

theorem integral_phase_R_nonneg (τ t : ℝ) (hτ : 0 ≤ τ) :
    (∫ x in (0:ℝ)..1, -Real.log ‖phase τ t x‖) =
      radialR τ-(complexR ((τ:ℂ)-(t:ℂ)*Complex.I)).re := by
  obtain rfl | hτ := hτ.eq_or_lt
  · simpa using integral_phase_zero_R t
  · exact integral_phase_eq_R_re_difference τ t hτ


theorem uniform_certificate_nonneg (τ T t c : ℝ) (b : ℕ → ℝ) (n : ℕ)
    (hτ : 0 ≤ τ) (hT : τ ≤ T) (hc : 0 ≤ c) (ht : c ≤ |t|)
    (hb : b 0 = 0) (hend : b n = 1) (hm : Monotone b) :
    Borwein.ResonantCertificate.certificate (Borwein.ResonantCertificate.heights b n T) b n c ≤
      radialR τ-(complexR ((τ:ℂ)-(t:ℂ)*Complex.I)).re := by
  rw [← integral_phase_R_nonneg τ t hτ]
  apply le_trans _ (integral_phase_gap_nonneg τ t hτ)
  apply le_trans _ (Borwein.ResonantCertificate.gap_integral_le_quadratic τ t)
  have hp (i : ℕ) : 0 ≤ b i := by simpa [hb] using hm (Nat.zero_le i)
  have hT0 := le_trans hτ hT
  apply Borwein.ResonantCertificate.certificate_le_gap_integral τ t c
    (Borwein.ResonantCertificate.heights b n T) b n hτ hc ht
    (Borwein.ResonantCertificate.heights_last b n T) hb hend
  · exact fun i _ => hm (Nat.le_succ i)
  · exact fun i _ => hp i
  · exact Borwein.ResonantCertificate.heights_decreasing b n T hT0 hb hm
  · intro d i hi
    simp only [Borwein.ResonantCertificate.heights, if_pos hi]
    exact Borwein.GroupedWeights.antitoneOn_envelope d
      (mul_nonneg hτ (hp _)) (mul_nonneg hT0 (hp _))
      (mul_le_mul_of_nonneg_right hT (hp _))

end
end Borwein.PhaseSingular
