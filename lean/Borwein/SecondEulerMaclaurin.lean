import Borwein.SecondPeano
import Borwein.EulerMaclaurin

namespace Borwein.SecondEulerMaclaurin
noncomputable section
open MeasureTheory Set PeanoQuadrature EulerMaclaurin
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem interval_error (a h α : ℝ) (hh : 0 < h) (ha0 : 0 ≤ α) (ha1 : α ≤ 1)
    (f0 f1 f2 : ℝ → F)
    (hf0 : ∀ u ∈ Icc a (a+h), HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u ∈ Icc a (a+h), HasDerivAt f1 (f2 u) u)
    (hf2 : ContinuousOn f2 (Icc a (a+h))) :
    ‖f0 (a+h*α)-h⁻¹ • (∫ u in a..a+h, f0 u)-B1 α • (f0 (a+h)-f0 a)‖ ≤
      (h/8)*(∫ u in a..a+h, ‖f2 u‖) := by
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
  have hg2 : ContinuousOn (fun u => h^2 • f2 (a+h*u)) (Icc (0:ℝ) 1) :=
    (hf2.comp (by fun_prop) hm).const_smul (h^2)
  have he := SecondPeano.cell_error α ha0 ha1 (fun u => f0 (a+h*u)) (fun u => h • f1 (a+h*u))
    (fun u => h^2 • f2 (a+h*u)) hg0 hg1 hg2
  have he2 : (∫ u in (0:ℝ)..1, ‖h^2 • f2 (a+h*u)‖) = h*(∫ u in a..a+h, ‖f2 u‖) := by
    simp_rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg h)]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_mul (fun u => ‖f2 u‖) hh.ne' a]
    simp only [mul_zero,add_zero,mul_one,smul_eq_mul]
    rw [← mul_assoc,show h^2*h⁻¹ = h by field_simp]
  rw [he2,intervalIntegral.integral_comp_add_mul f0 hh.ne' a] at he
  simp only [mul_zero,add_zero,mul_one] at he
  convert! he using 1
  ring

def residual (n : ℕ) (α : ℝ) (f0 : ℝ → F) (k : ℕ) : F :=
  f0 (((k:ℝ)+α)/n)-(n:ℝ) • (∫ u in node n k..node n (k+1), f0 u)-
    B1 α • (f0 (node n (k+1))-f0 (node n k))

theorem residual_bound (n : ℕ) (hn : 0 < n) (α : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1)
    (f0 f1 f2 : ℝ → F)
    (hf0 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f1 (f2 u) u)
    (hf2 : ContinuousOn f2 (Icc (0:ℝ) 1)) (k : ℕ) (hk : k < n) :
    ‖residual n α f0 k‖ ≤ ((n:ℝ)⁻¹/8)*(∫ u in node n k..node n (k+1), ‖f2 u‖) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hs : Icc (node n k) (node n k+(n:ℝ)⁻¹) ⊆ Icc (0:ℝ) 1 := by
    rw [← node_succ]
    exact Icc_subset_uIcc.trans (cell_subset n hn k hk)
  have he := interval_error (node n k) (n:ℝ)⁻¹ α (inv_pos.mpr hn') ha0 ha1 f0 f1 f2
    (fun u hu => hf0 u (hs hu)) (fun u hu => hf1 u (hs hu)) (hf2.mono hs)
  have hx : node n k+(n:ℝ)⁻¹*α = ((k:ℝ)+α)/n := by unfold node; field_simp
  simpa only [← node_succ,inv_inv,hx,residual] using he

omit [CompleteSpace F] in
theorem residual_sum (n : ℕ) (hn : 0 < n) (α : ℝ) (f0 : ℝ → F)
    (hf0 : ContinuousOn f0 (Icc (0:ℝ) 1)) :
    (∑ k ∈ Finset.range n, residual n α f0 k) =
      (∑ k ∈ Finset.range n, f0 (((k:ℝ)+α)/n))-(n:ℝ) • (∫ u in (0:ℝ)..1, f0 u)-
      B1 α • (f0 1-f0 0) := by
  have ht := differences_sum (fun k => f0 (node n k)) n
  simp only [Finset.sum_sub_distrib] at ht
  simp only [residual,Finset.sum_sub_distrib,← Finset.smul_sum]
  rw [integral_cells n hn f0 hf0,ht]
  simp [node,ne_of_gt hn]

theorem error_bound (n : ℕ) (hn : 0 < n) (α : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1)
    (f0 f1 f2 : ℝ → F)
    (hf0 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f1 (f2 u) u)
    (hf2 : ContinuousOn f2 (Icc (0:ℝ) 1)) :
    ‖(∑ k ∈ Finset.range n, f0 (((k:ℝ)+α)/n))-(n:ℝ) • (∫ u in (0:ℝ)..1, f0 u)-
      B1 α • (f0 1-f0 0)‖ ≤ (1/(8*(n:ℝ)))*(∫ u in (0:ℝ)..1, ‖f2 u‖) := by
  have hc : ContinuousOn f0 (Icc (0:ℝ) 1) := fun u hu => (hf0 u hu).continuousAt.continuousWithinAt
  rw [← residual_sum n hn α f0 hc]
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖residual n α f0 k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, ((n:ℝ)⁻¹/8)*(∫ u in node n k..node n (k+1), ‖f2 u‖) := by
      apply Finset.sum_le_sum
      intro k hk
      exact residual_bound n hn α ha0 ha1 f0 f1 f2 hf0 hf1 hf2 k (Finset.mem_range.mp hk)
    _ = _ := by
      rw [← Finset.mul_sum,integral_cells n hn (fun u => ‖f2 u‖) hf2.norm]
      congr 1
      ring

end
end Borwein.SecondEulerMaclaurin
