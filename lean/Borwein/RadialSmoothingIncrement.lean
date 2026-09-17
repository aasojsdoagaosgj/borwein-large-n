import Borwein.SmoothedResonantMain
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

namespace Borwein.RadialSmoothingIncrement
noncomputable section
open Complex MeasureTheory intervalIntegral

def entropy (c : ℝ) : ℝ := (1+c)*Real.log (1+c)-c*Real.log c

theorem radial_ratio (u : ℝ) (_hu : 0 < u) :
    u*Real.exp (-u) ≤ 1-Real.exp (-u) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp u) (Real.exp_pos (-u)).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at h
  nlinarith

theorem damping_difference (δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ 1-Real.exp (-δ) ∧ 1-Real.exp (-δ) ≤ δ := by
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  · linarith [Real.add_one_le_exp (-δ)]

theorem factor_upper (w : ℂ) (δ : ℝ) (hw : 0 < w.re) (hδ : 0 ≤ δ) :
    ‖1-Complex.exp (-((δ:ℂ)+w))‖ ≤ (1+δ/w.re)*‖1-Complex.exp (-w)‖ := by
  let r := Real.exp (-w.re)
  let d := ‖1-Complex.exp (-w)‖
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hn : ‖Complex.exp (-w)‖ = r := by simp [r,Complex.norm_exp]
  have hl : 1-r ≤ d := by
    have h := norm_sub_norm_le (1:ℂ) (Complex.exp (-w))
    simpa [hn,d] using h
  have hratio : w.re*r ≤ d := (radial_ratio w.re hw).trans hl
  have he : 1-Complex.exp (-((δ:ℂ)+w)) =
      (1-Complex.exp (-w))+(((1-Real.exp (-δ):ℝ):ℂ)*Complex.exp (-w)) := by
    rw [neg_add,Complex.exp_add,← Complex.ofReal_neg,← Complex.ofReal_exp]
    push_cast
    ring
  have htri := norm_add_le (1-Complex.exp (-w))
    (((1-Real.exp (-δ):ℝ):ℂ)*Complex.exp (-w))
  rw [he]
  apply htri.trans
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (damping_difference δ hδ).1,hn]
  have hm := mul_le_mul_of_nonneg_right (damping_difference δ hδ).2 hr
  have hδu : 0 ≤ δ/w.re := div_nonneg hδ hw.le
  have hmul := mul_le_mul_of_nonneg_left hratio hδu
  have hc : δ/w.re*(w.re*r) = δ*r := by field_simp
  rw [hc] at hmul
  change d+(1-Real.exp (-δ))*r ≤ (1+δ/w.re)*d
  nlinarith

theorem log_increment (w : ℂ) (δ : ℝ) (hw : 0 < w.re) (hδ : 0 ≤ δ) :
    Real.log ‖1-Complex.exp (-((δ:ℂ)+w))‖-Real.log ‖1-Complex.exp (-w)‖ ≤
      Real.log (1+δ/w.re) := by
  have hn : 1-Complex.exp (-w) ≠ 0 := by
    simpa [LogKernel.kernel] using LogKernel.kernel_ne_zero w 1 hw (by norm_num)
  have hns : 1-Complex.exp (-((δ:ℂ)+w)) ≠ 0 := by
    simpa [LogKernel.kernel] using LogKernel.kernel_ne_zero ((δ:ℂ)+w) 1 (by simpa using add_pos_of_nonneg_of_pos hδ hw) (by norm_num)
  have hc : 0 < 1+δ/w.re := by positivity
  have h := Real.log_le_log (norm_pos_iff.mpr hns) (factor_upper w δ hw hδ)
  rw [Real.log_mul hc.ne' (norm_ne_zero_iff.mpr hn)] at h
  linarith

theorem integrable_log_shift (c : ℝ) (hc : 0 < c) :
    IntervalIntegrable (fun x : ℝ => Real.log (x+c)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (a := (0:ℝ)) (b := 1) (by norm_num)
  apply ContinuousOn.log (by fun_prop)
  intro x hx
  exact ne_of_gt (by linarith [hx.1])

theorem log_ratio (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    Real.log (1+c/x) = Real.log (x+c)-Real.log x := by
  rw [← Real.log_div (by linarith : x+c ≠ 0) hx.ne']
  congr 1
  field_simp

theorem integrable_increment (c : ℝ) (hc : 0 < c) :
    IntervalIntegrable (fun x : ℝ => Real.log (1+c/x)) volume 0 1 := by
  have he : Set.EqOn (fun x : ℝ => Real.log (1+c/x))
      (fun x : ℝ => Real.log (x+c)-Real.log x) (Set.uIoo (0:ℝ) 1) := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0:ℝ) 1 := by simpa using hx
    exact log_ratio c x hc hx'.1
  exact (intervalIntegrable_congr_uIoo he).mpr ((integrable_log_shift c hc).sub intervalIntegrable_log')

theorem integral_increment (c : ℝ) (hc : 0 < c) :
    (∫ x in (0:ℝ)..1, Real.log (1+c/x)) = entropy c := by
  have he : (∫ x in (0:ℝ)..1, Real.log (1+c/x)) =
      ∫ x in (0:ℝ)..1, Real.log (x+c)-Real.log x := by
    apply intervalIntegral.integral_congr_ae
    apply ae_of_all
    intro x hx
    have hx' : x ∈ Set.Ioc (0:ℝ) 1 := by simpa using hx
    exact log_ratio c x hc hx'.1
  rw [he,intervalIntegral.integral_sub (integrable_log_shift c hc) intervalIntegrable_log',
    intervalIntegral.integral_comp_add_right,integral_log,integral_log]
  simp [entropy]
  ring

end
end Borwein.RadialSmoothingIncrement
