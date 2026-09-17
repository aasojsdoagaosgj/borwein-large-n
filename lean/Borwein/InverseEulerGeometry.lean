import Borwein.InverseEulerLoss
import Borwein.InverseEulerConstants
import Borwein.PeriodicRadialProfile

set_option autoImplicit false

namespace Borwein.InverseEulerGeometry
noncomputable section
open Complex InverseEulerLoss PeriodicRadialProfile

theorem geometric_identity (q : ℂ) (hq : ‖q‖ < 1) :
    geometricLoss q = (1+‖q‖)*(‖q‖-q.re)/((1-‖q‖)*‖1-q‖^2) := by
  have hn : 1-q ≠ 0 := by
    intro he
    have he' : q = 1 := (sub_eq_zero.mp he).symm
    simp [he'] at hq
  have hd : ‖1-q‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hn)
  have hr : 1-‖q‖ ≠ 0 := by linarith
  have hs : ‖q‖^2 = q.re^2+q.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have ht : ‖1-q‖^2 = 1-2*q.re+‖q‖^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    nlinarith
  have he : (q/(1-q)).re = (q.re-‖q‖^2)/‖1-q‖^2 := by
    rw [Complex.div_re, ← Complex.sq_norm]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    rw [← add_div]
    congr 1
    nlinarith
  rw [geometricLoss, he]
  field_simp
  nlinarith

theorem ray_real (x t : ℝ) : (ray x t).re = Real.exp (-x)*Real.cos t := by
  simp [ray, Complex.exp_re]

theorem ray_denominator (x t : ℝ) :
    ‖1-ray x t‖^2 = Real.exp (-x)*
      (Real.exp x+Real.exp (-x)-2+2*(1-Real.cos t)) := by
  have hs := Real.sin_sq_add_cos_sq t
  have hs' := congrArg (fun a : ℝ => (Real.exp (-x))^2*a) hs
  have he : Real.exp x*Real.exp (-x)=1 := by rw [← Real.exp_add]; simp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  simp [ray, Complex.exp_re, Complex.exp_im]
  nlinarith

theorem ray_loss (x t : ℝ) (hx : 0 < x) :
    geometricLoss (ray x t) =
      ((1+Real.exp (-x))/(1-Real.exp (-x)))*
        ((1-Real.cos t)/(Real.exp x+Real.exp (-x)-2+2*(1-Real.cos t))) := by
  have hq : ‖ray x t‖ < 1 := by
    rw [ray_norm]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  rw [geometric_identity _ hq, ray_norm, ray_real, ray_denominator]
  have he := Real.exp_ne_zero (-x)
  field_simp
  <;> ring

end
end Borwein.InverseEulerGeometry
