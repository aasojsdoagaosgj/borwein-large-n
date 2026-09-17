import Borwein.GaussianTail

set_option autoImplicit false

namespace Borwein.AbsoluteGaussianMoment
noncomputable section
open MeasureTheory Set

def primitive (c t : ℝ) : ℝ := -(c*t^2+1)*Real.exp (-c*t^2)/(2*c^2)
def integrand (c t : ℝ) : ℝ := |t|^3*Real.exp (-c*t^2)

theorem primitive_deriv (c t : ℝ) (hc : 0 < c) :
    HasDerivAt (primitive c) (t^3*Real.exp (-c*t^2)) t := by
  have hi := hasDerivAt_id t
  have hd := (((hi.pow 2).const_mul c).add_const 1).neg.mul
    (((hi.pow 2).const_mul (-c)).exp)
  apply (hd.div_const (2*c^2)).congr_deriv
  simp only [Pi.pow_apply, Pi.neg_apply, id_eq]
  field_simp
  ring

theorem positive_integral_bound (c h : ℝ) (hc : 0 < c) (hh : 0 ≤ h) :
    (∫ t in (0:ℝ)..h, integrand c t) ≤ 1/(2*c^2) := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0:ℝ) h) => primitive_deriv c t hc)
    ((by fun_prop : Continuous (fun t : ℝ => t^3*Real.exp (-c*t^2))).intervalIntegrable 0 h)
  have hf : (∫ t in (0:ℝ)..h, integrand c t) = ∫ t in (0:ℝ)..h, t^3*Real.exp (-c*t^2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 ≤ t := (show t ∈ Icc (0:ℝ) h from by simpa [uIcc_of_le hh] using ht).1
    simp [integrand, abs_of_nonneg ht0]
  rw [hf, he]
  have hp : primitive c h ≤ 0 := by
    unfold primitive
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (Real.exp_pos _).le
  have hz : primitive c 0=-(1/(2*c^2)) := by simp [primitive]; ring
  rw [hz]
  linarith

theorem integrand_even (c t : ℝ) : integrand c (-t)=integrand c t := by simp [integrand]

theorem absolute_cubic_bound (c h : ℝ) (hc : 0 < c) (hh : 0 ≤ h) :
    (∫ t in -h..h, integrand c t) ≤ 1/c^2 := by
  have hi : Continuous (integrand c) := by unfold integrand; fun_prop
  have he := intervalIntegral.integral_comp_neg (f := integrand c) (a := 0) (b := h)
  simp only [integrand_even, neg_zero] at he
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (-h) 0) (hi.intervalIntegrable 0 h), ← he]
  have hb := positive_integral_bound c h hc hh
  rw [show (1:ℝ)/(2*c^2)=(1/2)*(1/c^2) by ring] at hb
  linarith

end
end Borwein.AbsoluteGaussianMoment
