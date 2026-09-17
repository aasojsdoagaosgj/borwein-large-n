import Borwein.Dilogarithm

namespace Borwein.ComplexKernelBridge
noncomputable section
open Complex Set MeasureTheory LogKernel PhaseIntegral

theorem kernel_re_pos (z : ℂ) (x : ℝ) (hz : 0 < z.re) (hx : 0 < x) :
    0 < (kernel z x).re := by
  have he : ‖Complex.exp (-z*(x:ℂ))‖ < 1 := by
    rw [Complex.norm_exp,Real.exp_lt_one_iff]
    simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,
      Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hz) hx
  have h := (Complex.re_le_norm (Complex.exp (-z*(x:ℂ)))).trans_lt he
  simpa only [kernel,Complex.sub_re,Complex.one_re] using sub_pos.mpr h

theorem log_quotient (u v : ℂ) (hu : 0 < u.re) (hv : 0 < v.re) :
    Complex.log (u/v) = Complex.log u-Complex.log v := by
  have hsu : u ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hu)
  have hsv : v ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hv)
  have hau := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu))
  have hav := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hv))
  have he := Complex.log_exp (x := Complex.log u-Complex.log v)
    (by simp only [Complex.sub_im,Complex.log_im]; linarith [hau.1,hav.2])
    (by simp only [Complex.sub_im,Complex.log_im]; linarith [hau.2,hav.1])
  rw [Complex.exp_sub,Complex.exp_log (Complex.slitPlane_ne_zero hsu),
    Complex.exp_log (Complex.slitPlane_ne_zero hsv)] at he
  exact he

theorem log_fiveSum_eq_difference (z : ℂ) (x : ℝ) (hz : 0 < z.re) (hx : 0 < x) :
    Complex.log (fiveSum (z*(x:ℂ))) = Complex.log (kernel (5*z) x)-Complex.log (kernel z x) := by
  have hz5 : 0 < (5*z).re := by simpa using mul_pos (by norm_num : (0:ℝ) < 5) hz
  rw [(eq_div_iff (kernel_ne_zero z x hz hx)).mpr (fiveSum_mul_kernel z x)]
  exact log_quotient _ _ (kernel_re_pos _ x hz5 hx) (kernel_re_pos z x hz hx)

theorem complexR_eq_kernelR (z : ℂ) (hz : 0 < z.re) : complexR z = kernelR z := by
  unfold complexR kernelR hIntegral
  rw [← intervalIntegral.integral_sub (intervalIntegrable_clog_kernel (5*z) 0 1)
    (intervalIntegrable_clog_kernel z 0 1)]
  apply intervalIntegral.integral_congr_ae
  apply ae_of_all
  intro x hx
  have hxi : x ∈ Ioc (0:ℝ) 1 := by simpa using hx
  exact log_fiveSum_eq_difference z x hz hxi.1

theorem complexR_eq_dilog (z : ℂ) (hz : 0 < z.re) :
    complexR z =
      (Dilogarithm.dilog (Complex.exp (-(5*z)))-(Real.pi:ℂ)^2/6)/(5*z)-
      (Dilogarithm.dilog (Complex.exp (-z))-(Real.pi:ℂ)^2/6)/z := by
  rw [complexR_eq_kernelR z hz,Dilogarithm.kernelR_eq_dilog z hz]

end
end Borwein.ComplexKernelBridge
