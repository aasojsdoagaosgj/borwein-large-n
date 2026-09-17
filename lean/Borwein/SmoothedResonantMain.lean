import Borwein.SmoothedLogSeries
import Borwein.LogKernel
import Borwein.SmoothedPhase

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Borwein.SmoothedResonantMain
noncomputable section
open Complex MeasureTheory SmoothedLogSeries

def integral (b : ℕ) (η : ℝ) (z : ℂ) : ℂ := ∫ x in (0:ℝ)..1, logValue b η z x
def poleIntegral (b : ℕ) (η : ℝ) (z : ℂ) : ℝ :=
  ∫ x in (0:ℝ)..1, Real.log ‖1-Complex.exp (-(b:ℂ)*((η:ℂ)+z*(x:ℂ)))‖

theorem shifted_re_pos (b : ℕ) (η : ℝ) (z : ℂ) (x : ℝ)
    (hb : 0 < b) (hη : 0 < η) (hz : 0 ≤ z.re) (hx : 0 ≤ x) :
    0 < ((b:ℂ)*((η:ℂ)+z*(x:ℂ))).re := by
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,Complex.add_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero]
  positivity

theorem logValue_continuous (b : ℕ) (η : ℝ) (z : ℂ)
    (hb : 0 < b) (hη : 0 < η) (hz : 0 ≤ z.re) :
    ContinuousOn (logValue b η z) (Set.Icc (0:ℝ) 1) := by
  have hc : ContinuousOn (fun x : ℝ => Complex.log (1-Complex.exp (-(b:ℂ)*((η:ℂ)+z*(x:ℂ)))))
      (Set.Icc (0:ℝ) 1) := by
    apply ContinuousOn.clog (by fun_prop)
    intro x hx
    apply Complex.mem_slitPlane_iff.mpr
    left
    have he : ‖Complex.exp (-(b:ℂ)*((η:ℂ)+z*(x:ℂ)))‖ < 1 := by
      rw [Complex.norm_exp,Real.exp_lt_one_iff,neg_mul,Complex.neg_re]
      exact neg_neg_of_pos (shifted_re_pos b η z x hb hη hz hx.1)
    have hr := Complex.re_le_norm (Complex.exp (-(b:ℂ)*((η:ℂ)+z*(x:ℂ))))
    simp only [Complex.sub_re,Complex.one_re]
    linarith
  exact hc.neg.div_const _

theorem logValue_real (b : ℕ) (η : ℝ) (z : ℂ) (x : ℝ) :
    (logValue b η z x).re = -Real.log ‖1-Complex.exp (-(b:ℂ)*((η:ℂ)+z*(x:ℂ)))‖/(b:ℝ) := by
  simp [logValue,Complex.log_re]

theorem integral_real (b : ℕ) (η : ℝ) (z : ℂ)
    (hb : 0 < b) (hη : 0 < η) (hz : 0 ≤ z.re) :
    (integral b η z).re = -poleIntegral b η z/(b:ℝ) := by
  have hi := (logValue_continuous b η z hb hη hz).intervalIntegrable_of_Icc (μ := volume) (by norm_num)
  have hr : (∫ x in (0:ℝ)..1, logValue b η z x).re = ∫ x in (0:ℝ)..1, (logValue b η z x).re :=
    (intervalIntegral.intervalIntegral_re hi).symm
  rw [integral,hr]
  simp only [logValue_real,intervalIntegral.integral_div,intervalIntegral.integral_neg,poleIntegral]

theorem coprime_main (b : ℕ) (η : ℝ) (z : ℂ)
    (hb : 0 < b) (hη : 0 < η) (hz : 0 ≤ z.re) :
    -(4*integral b η z).re = (4/(b:ℝ))*poleIntegral b η z := by
  norm_num [Complex.mul_re,
    integral_real b η z hb hη hz]
  ring

theorem five_pointwise (B : ℕ) (η : ℝ) (z : ℂ) (x : ℝ)
    (hB : 0 < B) (hη : 0 < η) (hz : 0 ≤ z.re) (hx : 0 ≤ x) :
    (-5*logValue (5*B) η z x+logValue B η z x).re =
      Real.log ‖PhaseIntegral.fiveSum ((B:ℂ)*((η:ℂ)+z*(x:ℂ)))‖/(B:ℝ) := by
  have h := LogKernel.log_norm_fiveSum_eq_kernel_difference
    ((B:ℂ)*((η:ℂ)+z*(x:ℂ))) 1 (shifted_re_pos B η z x hB hη hz hx) (by norm_num)
  simp only [Complex.ofReal_one,mul_one,LogKernel.kernel] at h
  norm_num [Complex.add_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.natCast_re,Complex.natCast_im,neg_zero,zero_mul,sub_zero,logValue_real]
  rw [h]
  simp only [mul_assoc]
  field_simp
  ring

theorem five_integral (B : ℕ) (η : ℝ) (z : ℂ)
    (hB : 0 < B) (hη : 0 < η) (hz : 0 ≤ z.re) :
    -(5*integral (5*B) η z-integral B η z).re =
      (∫ x in (0:ℝ)..1, Real.log ‖PhaseIntegral.fiveSum ((B:ℂ)*((η:ℂ)+z*(x:ℂ)))‖)/(B:ℝ) := by
  have h1 := (logValue_continuous B η z hB hη hz).intervalIntegrable_of_Icc (μ := volume) (by norm_num)
  have h5 := (logValue_continuous (5*B) η z (by omega) hη hz).intervalIntegrable_of_Icc (μ := volume) (by norm_num)
  have hi := (h5.const_mul (-5:ℂ)).add h1
  have hr : (∫ x in (0:ℝ)..1, -5*logValue (5*B) η z x+logValue B η z x).re =
      ∫ x in (0:ℝ)..1, (-5*logValue (5*B) η z x+logValue B η z x).re :=
    (intervalIntegral.intervalIntegral_re hi).symm
  have he : -(5*integral (5*B) η z-integral B η z) =
      ∫ x in (0:ℝ)..1, -5*logValue (5*B) η z x+logValue B η z x := by
    rw [intervalIntegral.integral_add (h5.const_mul _) h1,intervalIntegral.integral_const_mul]
    unfold integral
    ring
  rw [← Complex.neg_re,he,hr,← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Set.Icc (0:ℝ) 1 := by simpa using hx
  exact five_pointwise B η z x hB hη hz hx'.1

theorem five_smoothed_modulus (B : ℕ) (η τ t : ℝ)
    (hB : 0 < B) (hη : 0 < η) (hτ : 0 ≤ τ) :
    -(5*integral (5*B) η ((τ:ℂ)-(t:ℂ)*I)-integral B η ((τ:ℂ)-(t:ℂ)*I)).re =
      SmoothedPhase.smoothedModulus ((B:ℝ)*η) ((B:ℝ)*τ) ((B:ℝ)*t)/(B:ℝ) := by
  rw [five_integral B η _ hB hη (by simpa using hτ)]
  unfold SmoothedPhase.smoothedModulus SmoothedPhase.smoothedSum
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  have he : (B:ℂ)*((η:ℂ)+((τ:ℂ)-(t:ℂ)*I)*(x:ℂ)) =
      ((((B:ℝ)*η+(B:ℝ)*τ*x):ℝ):ℂ)-(((((B:ℝ)*t*x):ℝ):ℂ)*I) := by
    push_cast
    ring
  dsimp only
  rw [he]

end
end Borwein.SmoothedResonantMain
