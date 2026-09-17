import Borwein.GaussianMoments
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace Borwein.GaussianTail
noncomputable section
open Set MeasureTheory GaussianMoments

theorem shifted_halfline (f : ℝ → ℝ) (h : ℝ) :
    (∫ x in Ioi (0:ℝ), f (x+h)) = ∫ x in Ioi h, f x := by
  have hm : MeasurableEmbedding (fun x : ℝ => x+h) :=
    (Homeomorph.addRight h).isClosedEmbedding.measurableEmbedding
  have he := hm.setIntegral_map (μ := volume) f (Ioi h)
  rw [map_add_right_eq_self] at he
  have hp : (fun x : ℝ => x+h) ⁻¹' Ioi h = Ioi 0 := by ext x; simp
  simpa only [hp] using he.symm

theorem shifted_gaussian_bound (c h x : ℝ) (hc : 0 ≤ c) (hh : 0 ≤ h) (hx : 0 ≤ x) :
    gaussian c (x+h) ≤ Real.exp (-c*h^2)*gaussian c x := by
  unfold gaussian
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (mul_nonneg hc hx) hh]

theorem halfline_tail_bound (c h : ℝ) (hc : 0 < c) (hh : 0 ≤ h) :
    (∫ x in Ioi h, gaussian c x) ≤ Real.exp (-c*h^2)*Real.sqrt (Real.pi/c)/2 := by
  rw [← shifted_halfline]
  have hg : Integrable (fun x : ℝ => Real.exp (-c*h^2)*gaussian c x) volume :=
    (integrable_gaussian c hc).const_mul _
  have hm := integral_mono_of_nonneg
    (μ := volume.restrict (Ioi (0:ℝ)))
    (f := fun x : ℝ => gaussian c (x+h))
    (g := fun x : ℝ => Real.exp (-c*h^2)*gaussian c x)
    (Filter.Eventually.of_forall (fun x => gaussian_nonneg c (x+h))) hg.integrableOn
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall
      (fun x hx => shifted_gaussian_bound c h x hc.le hh hx.le)))
  rw [integral_const_mul] at hm
  have he : (∫ x in Ioi (0:ℝ), gaussian c x) = Real.sqrt (Real.pi/c)/2 := integral_gaussian_Ioi c
  rw [he] at hm
  simpa only [mul_div_assoc] using hm

theorem full_minus_interval (c h : ℝ) (hc : 0 < c) :
    Real.sqrt (Real.pi/c)-(∫ x in -h..h, gaussian c x) = 2*(∫ x in Ioi h, gaussian c x) := by
  have hi := integrable_gaussian c hc
  have hsum := intervalIntegral.integral_Iic_add_Ioi (b := -h) hi.integrableOn hi.integrableOn
  have hdiff := intervalIntegral.integral_Ioi_sub_Ioi'
    (a := -h) (b := h) hi.integrableOn hi.integrableOn
  have hneg : (∫ x in Iic (-h), gaussian c x) = ∫ x in Ioi h, gaussian c x := by
    simpa only [gaussian_even] using (integral_comp_neg_Ioi h (gaussian c)).symm
  have hfull : (∫ x : ℝ, gaussian c x) = Real.sqrt (Real.pi/c) := integral_gaussian c
  rw [hneg,hfull] at hsum
  linarith

theorem interval_tail_bound (c h : ℝ) (hc : 0 < c) (hh : 0 ≤ h) :
    |(∫ x in -h..h, gaussian c x)-Real.sqrt (Real.pi/c)| ≤
      Real.sqrt (Real.pi/c)*Real.exp (-c*h^2) := by
  have he := full_minus_interval c h hc
  have ht0 : 0 ≤ ∫ x in Ioi h, gaussian c x := integral_nonneg (gaussian_nonneg c)
  have ht := halfline_tail_bound c h hc hh
  rw [abs_of_nonpos (by linarith)]
  linarith

end
end Borwein.GaussianTail
