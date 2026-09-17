import Borwein.PeanoBounds

namespace Borwein.PeanoQuadrature
noncomputable section
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem interval_error (a h α : ℝ) (hh : 0 < h) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (f0 f1 f2 f3 : ℝ → F)
    (hf0 : ∀ u ∈ Icc a (a+h), HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u ∈ Icc a (a+h), HasDerivAt f1 (f2 u) u)
    (hf2 : ∀ u ∈ Icc a (a+h), HasDerivAt f2 (f3 u) u)
    (hf3 : ContinuousOn f3 (Icc a (a+h))) :
    ‖f0 (a+h*α)-h⁻¹ • (∫ u in a..a+h, f0 u)-B1 α • (f0 (a+h)-f0 a)-
      (h*B2 α/2) • (f1 (a+h)-f1 a)‖ ≤ h^2*(∫ u in a..a+h, ‖f3 u‖) := by
  have hm : MapsTo (fun u : ℝ => a+h*u) (Icc (0:ℝ) 1) (Icc a (a+h)) := by
    intro u hu
    constructor <;> nlinarith [hu.1,hu.2]
  have hc (u : ℝ) : HasDerivAt (fun u : ℝ => a+h*u) h u := by
    simpa using ((hasDerivAt_id u).const_mul h).const_add a
  have hg0 : ∀ u ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun u => f0 (a+h*u)) (h • f1 (a+h*u)) u := by
    intro u hu
    simpa only [Function.comp_def] using (hf0 _ (hm hu)).scomp u (hc u)
  have hg1 : ∀ u ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun u => h • f1 (a+h*u)) (h^2 • f2 (a+h*u)) u := by
    intro u hu
    simpa [Function.comp_def,smul_smul,pow_two] using ((hf1 _ (hm hu)).scomp u (hc u)).fun_const_smul h
  have hg2 : ∀ u ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun u => h^2 • f2 (a+h*u)) (h^3 • f3 (a+h*u)) u := by
    intro u hu
    convert! ((hf2 _ (hm hu)).scomp u (hc u)).fun_const_smul (h^2) using 1 <;>
      simp only [Function.comp_def,smul_smul] <;> module
  have hg3 : ContinuousOn (fun u => h^3 • f3 (a+h*u)) (Icc (0:ℝ) 1) := by
    exact (hf3.comp (by fun_prop) hm).const_smul (h^3)
  have he := cell_error α hα0 hα1 (fun u => f0 (a+h*u)) (fun u => h • f1 (a+h*u))
    (fun u => h^2 • f2 (a+h*u)) (fun u => h^3 • f3 (a+h*u)) hg0 hg1 hg2 hg3
  have hn : (∫ u in (0:ℝ)..1, ‖h^3 • f3 (a+h*u)‖) = h^2*(∫ u in a..a+h, ‖f3 u‖) := by
    simp_rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hh.le 3)]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_mul (fun u => ‖f3 u‖) hh.ne' a]
    simp only [mul_zero,add_zero,mul_one,smul_eq_mul]
    rw [← mul_assoc,show h^3*h⁻¹ = h^2 by field_simp]
  rw [hn,intervalIntegral.integral_comp_add_mul f0 hh.ne' a] at he
  simp only [mul_zero,add_zero,mul_one] at he
  have hs : (B2 α/2) • (h • f1 (a+h)-h • f1 a) = (h*B2 α/2) • (f1 (a+h)-f1 a) := by module
  rw [hs] at he
  exact he

end
end Borwein.PeanoQuadrature
