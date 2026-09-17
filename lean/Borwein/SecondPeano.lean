import Borwein.PeanoBounds

namespace Borwein.SecondPeano
noncomputable section
open MeasureTheory Set PeanoQuadrature

def leftKernel (α u : ℝ) : ℝ := u^2/2-B1 α*u
def rightKernel (α u : ℝ) : ℝ := (1-u)^2/2+B1 α*(1-u)

theorem left_deriv (α u : ℝ) : HasDerivAt (leftKernel α) (left2 α u) u := by
  have hi := hasDerivAt_id u
  unfold leftKernel left2
  convert! ((hi.pow 2).div_const 2).sub (hi.const_mul (B1 α)) using 1
  norm_num

theorem right_deriv (α u : ℝ) : HasDerivAt (rightKernel α) (right2 α u) u := by
  have hi := (hasDerivAt_id u).const_sub 1
  unfold rightKernel right2
  convert! ((hi.pow 2).div_const 2).add (hi.const_mul (B1 α)) using 1
  norm_num
  ring

theorem left_bound (α u : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ α) :
    |leftKernel α u| ≤ 1/8 := by
  unfold leftKernel B1
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (u-α+1/2),mul_nonneg ha0 (sub_nonneg.mpr ha1)]
  · nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1),
      mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr ha1),sq_nonneg (α-1/2)]

theorem right_bound (α u : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1) (hu0 : α ≤ u) (hu1 : u ≤ 1) :
    |rightKernel α u| ≤ 1/8 := by
  have he : rightKernel α u = leftKernel (1-α) (1-u) := by unfold rightKernel leftKernel B1; ring
  rw [he]
  exact left_bound _ _ (by linarith) (by linarith) (by linarith) (by linarith)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem integrate_two (a b : ℝ) (p0 p1 : ℝ → ℝ) (f0 f1 f2 : ℝ → F)
    (hp0 : ∀ u, HasDerivAt p0 (p1 u) u) (hp1 : ∀ u, HasDerivAt p1 1 u)
    (hf0 : ∀ u ∈ uIcc a b, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u ∈ uIcc a b, HasDerivAt f1 (f2 u) u)
    (hi1 : IntervalIntegrable f1 volume a b) (hi2 : IntervalIntegrable f2 volume a b) :
    (∫ u in a..b, p0 u • f2 u) =
      p0 b • f1 b-p0 a • f1 a-p1 b • f0 b+p1 a • f0 a+(∫ u in a..b, f0 u) := by
  have hc1 : Continuous p1 := continuous_iff_continuousAt.mpr (fun u => (hp1 u).continuousAt)
  have h0 := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (fun u _ => hp0 u) hf1 (hc1.intervalIntegrable a b) hi2
  have h1 := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (fun u _ => hp1 u) hf0 (continuous_const.intervalIntegrable a b) hi1
  simp only [one_smul] at h1
  rw [h1] at h0
  rw [h0]
  abel

theorem cell_identity (α : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1) (f0 f1 f2 : ℝ → F)
    (hf0 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f1 (f2 u) u)
    (hf2 : ContinuousOn f2 (Icc (0:ℝ) 1)) :
    f0 α-(∫ u in (0:ℝ)..1, f0 u)-B1 α • (f0 1-f0 0) =
      -((∫ u in (0:ℝ)..α, leftKernel α u • f2 u)+(∫ u in α..1, rightKernel α u • f2 u)) := by
  have hleft : uIcc (0:ℝ) α ⊆ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le ha0]
    exact Icc_subset_Icc le_rfl ha1
  have hright : uIcc α (1:ℝ) ⊆ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le ha1]
    exact Icc_subset_Icc ha0 le_rfl
  have hc0 : ContinuousOn f0 (Icc (0:ℝ) 1) := fun u hu => (hf0 u hu).continuousAt.continuousWithinAt
  have hc1 : ContinuousOn f1 (Icc (0:ℝ) 1) := fun u hu => (hf1 u hu).continuousAt.continuousWithinAt
  have hl := integrate_two 0 α (leftKernel α) (left2 α) f0 f1 f2
    (left_deriv α) (left2_deriv α) (fun u hu => hf0 u (hleft hu)) (fun u hu => hf1 u (hleft hu))
    (hc1.mono hleft).intervalIntegrable (hf2.mono hleft).intervalIntegrable
  have hr := integrate_two α 1 (rightKernel α) (right2 α) f0 f1 f2
    (right_deriv α) (right2_deriv α) (fun u hu => hf0 u (hright hu)) (fun u hu => hf1 u (hright hu))
    (hc1.mono hright).intervalIntegrable (hf2.mono hright).intervalIntegrable
  have hj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc0.mono hleft).intervalIntegrable (hc0.mono hright).intervalIntegrable
  rw [hl,hr,← hj]
  simp only [leftKernel,rightKernel,left2,right2,B1]
  module

theorem weighted_norm_bound (p : ℝ → ℝ) (f : ℝ → F) (a b C : ℝ) (hab : a ≤ b)
    (hp : Continuous p) (hf : ContinuousOn f (Icc a b)) (hb : ∀ u ∈ Icc a b, |p u| ≤ C) :
    ‖∫ u in a..b, p u • f u‖ ≤ C*(∫ u in a..b, ‖f u‖) := by
  have hc : ContinuousOn (fun u => p u • f u) (Icc a b) := hp.continuousOn.smul hf
  calc
    _ ≤ ∫ u in a..b, ‖p u • f u‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ u in a..b, C*‖f u‖ := by
      apply intervalIntegral.integral_mono_on hab (hc.norm.intervalIntegrable_of_Icc hab)
        ((hf.norm.const_mul C).intervalIntegrable_of_Icc hab)
      intro u hu
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb u hu) (norm_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul C _

theorem cell_error (α : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1) (f0 f1 f2 : ℝ → F)
    (hf0 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f1 (f2 u) u)
    (hf2 : ContinuousOn f2 (Icc (0:ℝ) 1)) :
    ‖f0 α-(∫ u in (0:ℝ)..1, f0 u)-B1 α • (f0 1-f0 0)‖ ≤
      (1/8:ℝ)*(∫ u in (0:ℝ)..1, ‖f2 u‖) := by
  have hleft : Icc (0:ℝ) α ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc le_rfl ha1
  have hright : Icc α (1:ℝ) ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc ha0 le_rfl
  have hl := weighted_norm_bound (leftKernel α) f2 0 α (1/8) ha0 (by unfold leftKernel; fun_prop)
    (hf2.mono hleft) (fun u hu => left_bound α u ha0 ha1 hu.1 hu.2)
  have hr := weighted_norm_bound (rightKernel α) f2 α 1 (1/8) ha1 (by unfold rightKernel; fun_prop)
    (hf2.mono hright) (fun u hu => right_bound α u ha0 ha1 hu.1 hu.2)
  rw [cell_identity α ha0 ha1 f0 f1 f2 hf0 hf1 hf2,norm_neg]
  have hj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hf2.mono hleft).norm.intervalIntegrable_of_Icc ha0)
    ((hf2.mono hright).norm.intervalIntegrable_of_Icc ha1)
  have hb := (norm_add_le _ _).trans (add_le_add hl hr)
  rw [← mul_add,hj] at hb
  exact hb

end
end Borwein.SecondPeano
