import Borwein.PhaseBoundary
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

/-! Integrability of the endpoint-singular logarithmic kernel and the real h(5z)-h(z) bridge. -/

namespace Borwein.LogKernel
noncomputable section
open scoped BigOperators
open Borwein.PhaseIntegral Borwein.PhaseGap MeasureTheory

def kernel (z : ℂ) (x : ℝ) : ℂ := 1 - Complex.exp (-z*(x : ℂ))

theorem analyticAt_kernel (z : ℂ) (x : ℝ) : AnalyticAt ℝ (kernel z) x := by
  have ha : AnalyticAt ℂ (fun w : ℂ => 1 - Complex.exp (-z*w)) (x : ℂ) := by fun_prop
  exact ha.restrictScalars.comp (Complex.ofRealCLM.analyticAt x)

theorem continuous_kernel (z : ℂ) : Continuous (kernel z) := by
  unfold kernel
  fun_prop

/-- The logarithmic singularity at x=0 is handled by the meromorphic integrability theorem. -/
theorem intervalIntegrable_log_norm_kernel (z : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun x => Real.log ‖kernel z x‖) volume a b := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro x _
  exact (analyticAt_kernel z x).meromorphicAt

theorem intervalIntegrable_clog_of_log_norm (f : ℝ → ℂ) (a b : ℝ) (hf : Continuous f)
    (hi : IntervalIntegrable (fun x => Real.log ‖f x‖) volume a b) :
    IntervalIntegrable (fun x => Complex.log (f x)) volume a b := by
  have hb : IntervalIntegrable (fun x => |Real.log ‖f x‖| + Real.pi) volume a b :=
    hi.abs.add intervalIntegrable_const
  apply hb.mono_fun' (Complex.measurable_log.comp hf.measurable).aestronglyMeasurable
  apply ae_of_all
  intro x
  calc
    ‖Complex.log (f x)‖ ≤ |(Complex.log (f x)).re| + |(Complex.log (f x)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ |Real.log ‖f x‖| + Real.pi := by
      rw [Complex.log_re, Complex.log_im]
      exact add_le_add le_rfl (Complex.abs_arg_le_pi _)

theorem intervalIntegrable_clog_kernel (z : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun x => Complex.log (kernel z x)) volume a b :=
  intervalIntegrable_clog_of_log_norm _ a b (continuous_kernel z)
    (intervalIntegrable_log_norm_kernel z a b)

def hIntegral (z : ℂ) : ℂ := ∫ x in (0 : ℝ)..1, Complex.log (kernel z x)

theorem re_hIntegral (z : ℂ) :
    (hIntegral z).re = ∫ x in (0 : ℝ)..1, Real.log ‖kernel z x‖ := by
  symm
  simpa [hIntegral, Complex.log_re] using
    intervalIntegral.intervalIntegral_re (intervalIntegrable_clog_kernel z 0 1)

theorem kernel_ne_zero (z : ℂ) (x : ℝ) (hz : 0 < z.re) (hx : 0 < x) :
    kernel z x ≠ 0 := by
  intro hzero
  have he : Complex.exp (-z*(x : ℂ)) = 1 := (sub_eq_zero.mp hzero).symm
  have hn := congrArg norm he
  rw [Complex.norm_exp, norm_one] at hn
  have hre : (-z*(x : ℂ)).re < 0 := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hz) hx
  have := Real.exp_lt_one_iff.mpr hre
  linarith

theorem fiveSum_mul_kernel (z : ℂ) (x : ℝ) :
    fiveSum (z*(x : ℂ)) * kernel z x = kernel (5*z) x := by
  unfold fiveSum kernel
  rw [Fin.sum_univ_eq_sum_range]
  have he : -(z*(x : ℂ)) = -z*(x : ℂ) := by ring
  rw [he, geom_sum_mul_neg, ← Complex.exp_nat_mul]
  congr 2
  norm_num
  ring

theorem log_norm_fiveSum_eq_kernel_difference (z : ℂ) (x : ℝ)
    (hz : 0 < z.re) (hx : 0 < x) :
    Real.log ‖fiveSum (z*(x : ℂ))‖ =
      Real.log ‖kernel (5*z) x‖ - Real.log ‖kernel z x‖ := by
  have hk := kernel_ne_zero z x hz hx
  have hk5 := kernel_ne_zero (5*z) x (by simpa using mul_pos (by norm_num : (0:ℝ)<5) hz) hx
  have hf : fiveSum (z*(x : ℂ)) ≠ 0 := by
    intro hzero
    have h := fiveSum_mul_kernel z x
    rw [hzero, zero_mul] at h
    exact hk5 h.symm
  apply eq_sub_iff_add_eq.mpr
  rw [← Real.log_mul (norm_ne_zero_iff.mpr hf) (norm_ne_zero_iff.mpr hk),
    ← norm_mul, fiveSum_mul_kernel]

/-- Exact real-part equality with the singular kernel representation of h. -/
theorem modulusR_eq_re_h_difference (z : ℂ) (hz : 0 < z.re) :
    modulusR z = (hIntegral (5*z) - hIntegral z).re := by
  rw [Complex.sub_re, re_hIntegral, re_hIntegral, ← intervalIntegral.integral_sub
    (intervalIntegrable_log_norm_kernel (5*z) 0 1) (intervalIntegrable_log_norm_kernel z 0 1)]
  unfold modulusR
  apply intervalIntegral.integral_congr_ae
  apply ae_of_all
  intro x hx
  have hxi : x ∈ Set.Ioc (0 : ℝ) 1 := by simpa using hx
  exact log_norm_fiveSum_eq_kernel_difference z x hz hxi.1

theorem R_h_difference_ge_quadratic (τ t : ℝ) (hτ : 0 < τ) :
    (∫ x in (0 : ℝ)..1, gapDensity τ t x + gapDensity τ t x ^ 2) ≤
      radialR τ - (hIntegral (5*((τ : ℂ) - (t : ℂ)*Complex.I)) -
        hIntegral ((τ : ℂ) - (t : ℂ)*Complex.I)).re := by
  rw [← modulusR_eq_re_h_difference _ (by simpa using hτ)]
  exact R_difference_ge_quadratic τ t hτ

theorem modulusR_real (τ : ℝ) : modulusR (τ : ℂ) = radialR τ := by
  unfold modulusR radialR
  apply intervalIntegral.integral_congr
  intro x _
  change Real.log ‖fiveSum ((τ : ℂ)*(x : ℂ))‖ = Real.log (radialSum (τ*x))
  rw [← Complex.ofReal_mul, fiveSum_real, Complex.norm_real,
    Real.norm_of_nonneg (show 0 ≤ radialSum (τ*x) from (radialDenominator_pos (τ*x)).le)]

def kernelR (z : ℂ) : ℂ := hIntegral (5*z) - hIntegral z

theorem radialR_eq_re_kernelR (τ : ℝ) (hτ : 0 < τ) :
    radialR τ = (kernelR (τ : ℂ)).re := by
  rw [← modulusR_real, modulusR_eq_re_h_difference _ (by simpa using hτ)]
  rfl

/-- Both sides now use R=h(5z)-h(z), where h is the proved-integrable logarithmic kernel. -/
theorem kernelR_re_difference_ge_quadratic (τ t : ℝ) (hτ : 0 < τ) :
    (∫ x in (0 : ℝ)..1, gapDensity τ t x + gapDensity τ t x ^ 2) ≤
      (kernelR (τ : ℂ)).re - (kernelR ((τ : ℂ) - (t : ℂ)*Complex.I)).re := by
  rw [← radialR_eq_re_kernelR τ hτ]
  exact R_h_difference_ge_quadratic τ t hτ

end
end Borwein.LogKernel
