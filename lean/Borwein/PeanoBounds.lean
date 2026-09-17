import Borwein.PeanoQuadrature

namespace Borwein.PeanoQuadrature
noncomputable section
open MeasureTheory Set

theorem B1_abs (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) : |B1 α| ≤ 1/2 := by
  unfold B1
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem B2_abs (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) : |B2 α| ≤ 1/6 := by
  unfold B2
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (α-1/2)]
  · nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

theorem right0_abs (α u : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |right0 α u| ≤ 1/2 := by
  have ht0 : 0 ≤ 1-u := sub_nonneg.mpr hu1
  have ht1 : 1-u ≤ 1 := by linarith
  have hp2 : (1-u)^2 ≤ 1 := by simpa using pow_le_pow_left₀ ht0 ht1 2
  have hp3 : (1-u)^3 ≤ 1 := by simpa using pow_le_pow_left₀ ht0 ht1 3
  have h0 : |-(1-u)^3/6| ≤ 1/6 := by
    rw [neg_div,abs_neg,abs_of_nonneg (by positivity : 0 ≤ (1-u)^3/6)]
    linarith
  have h1 : |B1 α*(1-u)^2/2| ≤ 1/4 := by
    have hm := mul_le_mul (B1_abs α ha0 ha1) hp2 (sq_nonneg (1-u)) (by norm_num : (0:ℝ) ≤ 1/2)
    rw [abs_div,abs_mul,abs_pow,abs_of_nonneg ht0]
    norm_num
    linarith
  have h2 : |B2 α*(1-u)/2| ≤ 1/12 := by
    have hm := mul_le_mul (B2_abs α ha0 ha1) ht1 ht0 (by norm_num : (0:ℝ) ≤ 1/6)
    rw [abs_div,abs_mul,abs_of_nonneg ht0]
    norm_num
    linarith
  have hfirst := abs_add_le (-(1-u)^3/6) (-(B1 α*(1-u)^2/2))
  have hlast := abs_add_le (-(1-u)^3/6-B1 α*(1-u)^2/2) (-(B2 α*(1-u)/2))
  simp only [← sub_eq_add_neg,abs_neg] at hfirst hlast
  unfold right0
  linarith

theorem left0_abs (α u : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |left0 α u| ≤ 1 := by
  have hd : |α-u| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hp : (α-u)^2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg (α-u)) hd 2
    simpa using h
  have ht : |(α-u)^2/2| ≤ 1/2 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ (α-u)^2/2)]
    linarith
  have h := abs_add_le ((α-u)^2/2) (right0 α u)
  have hr := right0_abs α u ha0 ha1 hu0 hu1
  unfold left0
  linarith

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem cell_error (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (f0 f1 f2 f3 : ℝ → F)
    (hf0 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f1 (f2 u) u)
    (hf2 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f2 (f3 u) u)
    (hf3 : ContinuousOn f3 (Icc (0:ℝ) 1)) :
    ‖f0 α-(∫ u in (0:ℝ)..1, f0 u)-B1 α • (f0 1-f0 0)-(B2 α/2) • (f1 1-f1 0)‖ ≤
      ∫ u in (0:ℝ)..1, ‖f3 u‖ := by
  rw [cell_identity α hα0 hα1 f0 f1 f2 f3 hf0 hf1 hf2 hf3]
  have hleft : uIcc (0:ℝ) α ⊆ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hα0]
    exact Icc_subset_Icc le_rfl hα1
  have hright : uIcc α (1:ℝ) ⊆ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hα1]
    exact Icc_subset_Icc hα0 le_rfl
  have hl : ‖∫ u in (0:ℝ)..α, left0 α u • f3 u‖ ≤ ∫ u in (0:ℝ)..α, ‖f3 u‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le hα0 _ (hf3.norm.mono hleft).intervalIntegrable
    apply Filter.Eventually.of_forall
    intro u hu
    rw [norm_smul,Real.norm_eq_abs]
    have hc := left0_abs α u hα0 hα1 hu.1.le (hu.2.trans hα1)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg (f3 u))
  have hr : ‖∫ u in α..1, right0 α u • f3 u‖ ≤ ∫ u in α..1, ‖f3 u‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le hα1 _ (hf3.norm.mono hright).intervalIntegrable
    apply Filter.Eventually.of_forall
    intro u hu
    rw [norm_smul,Real.norm_eq_abs]
    have hc := (right0_abs α u hα0 hα1 (hα0.trans hu.1.le) hu.2).trans (by norm_num : (1/2:ℝ) ≤ 1)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg (f3 u))
  calc
    _ ≤ ‖∫ u in (0:ℝ)..α, left0 α u • f3 u‖+‖∫ u in α..1, right0 α u • f3 u‖ := norm_add_le _ _
    _ ≤ (∫ u in (0:ℝ)..α, ‖f3 u‖)+(∫ u in α..1, ‖f3 u‖) := add_le_add hl hr
    _ = _ := intervalIntegral.integral_add_adjacent_intervals
      (hf3.norm.mono hleft).intervalIntegrable (hf3.norm.mono hright).intervalIntegrable

end
end Borwein.PeanoQuadrature
