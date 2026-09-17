import Borwein.RadialSmoothingIncrement

set_option autoImplicit false

namespace Borwein.IntegratedSmoothingIncrement
noncomputable section
open Complex MeasureTheory RadialSmoothingIncrement SmoothedResonantMain LogKernel

theorem pole_integrable (b : ℕ) (η : ℝ) (z : ℂ) :
    IntervalIntegrable (fun x : ℝ => Real.log ‖1-Complex.exp (-(b:ℂ)*((η:ℂ)+z*(x:ℂ)))‖) volume 0 1 := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro x _
  have ha : AnalyticAt ℂ (fun w : ℂ => 1-Complex.exp (-(b:ℂ)*((η:ℂ)+z*w))) (x:ℂ) := by fun_prop
  exact (ha.restrictScalars.comp (Complex.ofRealCLM.analyticAt x)).meromorphicAt

theorem pointwise_increment (b : ℕ) (η : ℝ) (z : ℂ) (x : ℝ)
    (hb : 0 < b) (hη : 0 < η) (hz : 0 < z.re) (hx : 0 < x) :
    Real.log ‖1-Complex.exp (-(b:ℂ)*((η:ℂ)+z*(x:ℂ)))‖ ≤
      Real.log ‖kernel ((b:ℂ)*z) x‖+Real.log (1+(η/z.re)/x) := by
  have hw : 0 < (((b:ℂ)*z)*(x:ℂ)).re := by simp; positivity
  have h := log_increment (((b:ℂ)*z)*(x:ℂ)) ((b:ℝ)*η) hw (by positivity)
  have he : -(((((b:ℝ)*η):ℝ):ℂ)+((b:ℂ)*z)*(x:ℂ)) = -(b:ℂ)*((η:ℂ)+z*(x:ℂ)) := by
    push_cast
    ring
  rw [he] at h
  have hr : ((b:ℝ)*η)/(((b:ℂ)*z)*(x:ℂ)).re = (η/z.re)/x := by
    simp only [Complex.mul_re,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
    field_simp
  rw [hr] at h
  unfold kernel
  simp only [neg_mul] at h ⊢
  linarith

theorem pole_upper (b : ℕ) (η : ℝ) (z : ℂ)
    (hb : 0 < b) (hη : 0 < η) (hz : 0 < z.re) :
    poleIntegral b η z ≤ (hIntegral ((b:ℂ)*z)).re+entropy (η/z.re) := by
  rw [re_hIntegral,← integral_increment (η/z.re) (by positivity)]
  rw [← intervalIntegral.integral_add (intervalIntegrable_log_norm_kernel _ 0 1)
    (integrable_increment (η/z.re) (by positivity))]
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
    (pole_integrable b η z) ((intervalIntegrable_log_norm_kernel _ 0 1).add
      (integrable_increment (η/z.re) (by positivity)))
  intro x hx
  exact pointwise_increment b η z x hb hη hz hx.1

theorem entropy_mono {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) : entropy c ≤ entropy d := by
  rw [← integral_increment c hc,← integral_increment d (hc.trans_le hcd)]
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
    (integrable_increment c hc) (integrable_increment d (hc.trans_le hcd))
  intro x hx
  have hx0 : 0 < x := hx.1
  apply Real.log_le_log (by positivity)
  exact add_le_add le_rfl (div_le_div_of_nonneg_right hcd hx.1.le)

end
end Borwein.IntegratedSmoothingIncrement
