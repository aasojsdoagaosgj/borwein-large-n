import Borwein.WedgeRootKernel
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

namespace Borwein.WedgePoleDifference
noncomputable section
open Complex Set WedgeRootKernel

theorem scale_wedge (z : ℂ) (hz : 0 ≤ z.re) (hi : |z.im| ≤ 3*z.re/4)
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ ((t:ℂ)*z).re ∧ |((t:ℂ)*z).im| ≤ 3*((t:ℂ)*z).re/4 := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, abs_mul, abs_of_nonneg ht]
  constructor
  · exact mul_nonneg ht hz
  · nlinarith [mul_le_mul_of_nonneg_left hi ht]

theorem line_hasDerivAt (ξ z : ℂ) (hξ : ξ^5=1) (hne : ξ ≠ 1)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 3*z.re/4) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun t : ℝ => pole ξ ((t:ℂ)*z))
      (z * (-ξ*exp (-((t:ℂ)*z))/(1-ξ*exp (-((t:ℂ)*z)))^2)) t := by
  have hscale := scale_wedge z hz hi t ht
  have hd := pole_hasDerivAt ξ ((t:ℂ)*z) hξ hne hscale.1 hscale.2
  have hcast : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 t := by
    convert! Complex.ofRealCLM.hasDerivAt (x := t) using 1
  simpa only [Function.comp_def, one_mul, smul_eq_mul] using hd.scomp t (hcast.mul_const z)

theorem difference_bound (ξ z : ℂ) (hξ : ξ^5=1) (hne : ξ ≠ 1)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 3*z.re/4) :
    ‖pole ξ z-pole ξ 0‖ ≤ 4*‖z‖ := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (line_hasDerivAt ξ z hξ hne hz hi t ht.1).hasDerivWithinAt)
    (fun t ht => show
      ‖z * (-ξ*exp (-((t:ℂ)*z))/(1-ξ*exp (-((t:ℂ)*z)))^2)‖ ≤ 4*‖z‖ from by
      have hs := scale_wedge z hz hi t ht.1
      have hb := kernel_derivative_bound ξ ((t:ℂ)*z) hξ hne hs.1 hs.2
      rw [norm_mul, neg_mul, neg_div, norm_neg]
      nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg z)])
  simpa using h

theorem difference_at_zero (ξ z : ℂ) (hξ : ξ^5=1) (hne : ξ ≠ 1)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 3*z.re/4) :
    ‖pole ξ z-ξ/(1-ξ)‖ ≤ 4*‖z‖ := by
  simpa only [pole, neg_zero, exp_zero, mul_one] using difference_bound ξ z hξ hne hz hi

end
end Borwein.WedgePoleDifference
