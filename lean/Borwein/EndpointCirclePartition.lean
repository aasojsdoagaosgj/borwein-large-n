import Borwein.EndpointCircleKernel

set_option autoImplicit false

namespace Borwein.EndpointCirclePartition
noncomputable section
open Complex MeasureTheory EndpointCircleKernel

def boundary (j : ℕ) : ℝ := (2*(j:ℝ)-1)*Real.pi/5
def localSum (f : ℝ → ℂ) (h : ℝ) : ℂ := ∑ j : Fin 5,
  ∫ θ in angle j.val-h..angle j.val+h, f θ
def outerSum (f : ℝ → ℂ) (h : ℝ) : ℂ := ∑ j : Fin 5,
  ((∫ θ in boundary j.val..angle j.val-h, f θ)+
    (∫ θ in angle j.val+h..boundary (j.val+1), f θ))

theorem boundary_left (j : ℕ) : boundary j=angle j-Real.pi/5 := by unfold boundary angle; ring
theorem boundary_right (j : ℕ) : boundary (j+1)=angle j+Real.pi/5 := by unfold boundary angle; push_cast; ring
theorem boundary_period : boundary 0+2*Real.pi=boundary 5 := by unfold boundary; norm_num; ring

theorem cell_partition (f : ℝ → ℂ) (hf : Continuous f) (j : ℕ) (h : ℝ) :
    (∫ θ in boundary j..boundary (j+1), f θ) =
      (∫ θ in angle j-h..angle j+h, f θ)+
        ((∫ θ in boundary j..angle j-h, f θ)+(∫ θ in angle j+h..boundary (j+1), f θ)) := by
  rw [CoefficientArcSplit.interval_difference f hf (boundary j) (boundary (j+1)),
    CoefficientArcSplit.interval_difference f hf (angle j-h) (angle j+h),
    CoefficientArcSplit.interval_difference f hf (boundary j) (angle j-h),
    CoefficientArcSplit.interval_difference f hf (angle j+h) (boundary (j+1))]
  ring

theorem full_partition (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f (2*Real.pi)) (h : ℝ) :
    (∫ θ in (0:ℝ)..2*Real.pi, f θ)=localSum f h+outerSum f h := by
  have hP := hp.intervalIntegral_add_eq (boundary 0) 0
  rw [boundary_period, zero_add] at hP
  rw [← hP]
  have hS := intervalIntegral.sum_integral_adjacent_intervals (a := boundary) (n := 5)
    (f := f) (μ := volume) (fun j _ => hf.intervalIntegrable (boundary j) (boundary (j+1)))
  rw [← Fin.sum_univ_eq_sum_range] at hS
  rw [← hS]
  calc
    _ = ∑ j : Fin 5, ((∫ θ in angle j.val-h..angle j.val+h, f θ)+
        ((∫ θ in boundary j.val..angle j.val-h, f θ)+(∫ θ in angle j.val+h..boundary (j.val+1), f θ))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact cell_partition f hf j.val h
    _ = _ := Finset.sum_add_distrib

theorem local_reflection (f : ℝ → ℂ) (j : ℕ) (h : ℝ) :
    (∫ θ in angle j-h..angle j+h, f θ)=(∫ y in -h..h, f (angle j-y)) := by
  simpa only [sub_neg_eq_add] using (intervalIntegral.integral_comp_sub_left (a := -h) (b := h) f (angle j)).symm

theorem local_weighted (F : ℂ → ℂ) (m : ℕ) (v h : ℝ)
    (hF : Continuous (fun θ => F (point v θ))) :
    localSum (kernel F m v) h=(∫ y in -h..h, weighted F (m%5) v y*exp ((m:ℂ)*EndpointPhaseAtoms.coordinate v y)) := by
  have hK := kernel_continuous F m v hF
  unfold localSum
  simp_rw [local_reflection]
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr
    intro y _
    exact sum_rotated F m v y
  · intro j _
    have hc : Continuous (fun y : ℝ => kernel F m v (angle j.val-y)) := hK.comp (by fun_prop)
    exact hc.intervalIntegrable _ _

end
end Borwein.EndpointCirclePartition
