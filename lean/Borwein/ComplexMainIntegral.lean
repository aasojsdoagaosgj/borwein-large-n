import Borwein.FifthRootLogarithm
import Mathlib.Analysis.Calculus.MeanValue

namespace Borwein.ComplexMainIntegral
noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory LogFactorDerivatives FiveRootProductExpansion FifthRootLogarithm

def vertical (z : ℂ) (t : ℝ) : ℂ := (z.re:ℂ)+(t:ℂ)*(z.im:ℂ)*I

theorem vertical_zero (z : ℂ) : vertical z 0 = (z.re:ℂ) := by simp [vertical]
theorem vertical_one (z : ℂ) : vertical z 1 = z := by
  apply Complex.ext <;> simp [vertical]

theorem vertical_box (z : ℂ) (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    0 ≤ (vertical z t).re ∧ |(vertical z t).im| ≤ 2/5 := by
  simp only [vertical,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,mul_one,
    sub_self,Complex.add_im,zero_add]
  constructor
  · exact hz
  · rw [abs_mul,abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_left hi ht.1).trans (by nlinarith [ht.2])

def verticalDerivative (c z : ℂ) (x t : ℝ) : ℂ :=
  (z.im:ℂ)*I*(x:ℂ)*w c (vertical z t) x/kernel c (vertical z t) x

theorem vertical_log_deriv (c z : ℂ) (x t : ℝ)
    (hs : kernel c (vertical z t) x ∈ Complex.slitPlane) :
    HasDerivAt (fun t => f0 c (vertical z t) x) (verticalDerivative c z x t) t := by
  have hi : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 t := by
    convert! Complex.ofRealCLM.hasDerivAt (x := t) using 1
  have hv : HasDerivAt (vertical z) ((z.im:ℂ)*I) t := by
    unfold vertical
    convert! ((hi.mul_const (z.im:ℂ)).mul_const I).const_add (z.re:ℂ) using 1 <;> ring
  have hw : HasDerivAt (fun t => w c (vertical z t) x)
      (-((z.im:ℂ)*I*(x:ℂ))*w c (vertical z t) x) t := by
    unfold w
    convert! (((hv.neg).mul_const (x:ℂ)).cexp).const_mul c using 1 <;>
      simp only [Pi.neg_apply] <;> ring
  have hk : HasDerivAt (fun t => kernel c (vertical z t) x)
      ((z.im:ℂ)*I*(x:ℂ)*w c (vertical z t) x) t := by
    unfold kernel
    convert! hw.const_sub 1 using 1 <;> ring
  exact hk.clog_real hs

theorem vertical_derivative_bound (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) (j : Fin 4)
    (x t : ℝ) (hx : x ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖verticalDerivative (coefficients ξ j) z x t‖ ≤ 8/15 := by
  have hb := vertical_box z hz hi t ht
  have hw := w_norm_le_one (coefficients ξ j) (vertical z t) x
    (coefficients_norm ξ (root_norm ξ hξ.pow_eq_one).le j) hb.1 hx.1
  have hg := FifthRootSeparation.coefficient_gap ξ (vertical z t) hξ hb.2 j x hx
  calc
    _ = |z.im| * x*‖w (coefficients ξ j) (vertical z t) x‖ /
        ‖kernel (coefficients ξ j) (vertical z t) x‖ := by
      simp [verticalDerivative,norm_div,norm_mul,Real.norm_eq_abs,abs_of_nonneg hx.1]
    _ ≤ (2/5:ℝ)*1*1/(3/4) := by
      gcongr
      · exact hx.1
      · exact hx.2
    _ = 8/15 := by norm_num

theorem rootLog_vertical_bound (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    ‖rootLog ξ z x-rootLog ξ (z.re:ℂ) x‖ ≤ 32/15 := by
  have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun t => rootLog ξ (vertical z t) x)
        (∑ j : Fin 4, verticalDerivative (coefficients ξ j) z x t) t := by
    apply HasDerivAt.fun_sum
    intro j _
    have hb := vertical_box z hz hi t ht
    exact vertical_log_deriv _ z x t (coefficient_slit ξ _ hξ hb.1 hb.2 j x hx)
  have hb (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) :
      ‖∑ j : Fin 4, verticalDerivative (coefficients ξ j) z x t‖ ≤ (32/15:ℝ) := by
    have h := (norm_sum_le (Finset.univ : Finset (Fin 4)) _).trans (Finset.sum_le_sum
      (fun (j : Fin 4) _ => vertical_derivative_bound ξ z hξ hz hi j x t hx ⟨ht.1,ht.2.le⟩))
    norm_num at h
    exact h
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hd t ht).hasDerivWithinAt) hb
  simpa only [vertical_one,vertical_zero] using h

theorem rootLog_im_bound (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    |(rootLog ξ z x).im| ≤ 32/15 := by
  have h := (Complex.abs_im_le_norm (rootLog ξ z x-rootLog ξ (z.re:ℂ) x)).trans
    (rootLog_vertical_bound ξ z hξ hz hi x hx)
  simpa only [Complex.sub_im,rootLog_real_im ξ hξ z.re x hz hx,sub_zero] using h

theorem rootLog_eq_log_fiveSum (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    rootLog ξ z x = Complex.log (PhaseIntegral.fiveSum (z*(x:ℂ))) := by
  have hb := abs_le.mp (rootLog_im_bound ξ z hξ hz hi x hx)
  have hp := Real.pi_gt_three
  have he := Complex.log_exp (x := rootLog ξ z x) (by linarith [hb.1]) (by linarith [hb.2])
  rw [exp_rootLog ξ z hξ hi x hx] at he
  exact he.symm

theorem rootIntegral_eq_complexR (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) :
    rootIntegral ξ z = PhaseIntegral.complexR z := by
  rw [rootIntegral_eq_integral ξ z hξ hz hi,PhaseIntegral.complexR]
  apply intervalIntegral.integral_congr
  intro x hx
  exact rootLog_eq_log_fiveSum ξ z hξ hz hi x (by simpa using hx)

end
end Borwein.ComplexMainIntegral
