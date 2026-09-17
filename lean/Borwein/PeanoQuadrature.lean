import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

namespace Borwein.PeanoQuadrature
noncomputable section
open MeasureTheory Set

def B1 (α : ℝ) := α-1/2
def B2 (α : ℝ) := α^2-α+1/6
def right0 (α u : ℝ) := -(1-u)^3/6-B1 α*(1-u)^2/2-B2 α*(1-u)/2
def right1 (α u : ℝ) := (1-u)^2/2+B1 α*(1-u)+B2 α/2
def right2 (α u : ℝ) := u-1-B1 α
def left0 (α u : ℝ) := (α-u)^2/2+right0 α u
def left1 (α u : ℝ) := -(α-u)+right1 α u
def left2 (α u : ℝ) := u-B1 α

theorem right0_deriv (α u : ℝ) : HasDerivAt (right0 α) (right1 α u) u := by
  have hi : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id u
  unfold right0 right1
  have h := (((((hi.const_sub 1).pow 3).neg.div_const 6).sub
    (((hi.const_sub 1).pow 2).const_mul (B1 α) |>.div_const 2)).sub
    ((hi.const_sub 1).const_mul (B2 α) |>.div_const 2))
  convert! h using 1 <;> norm_num <;> ring

theorem right1_deriv (α u : ℝ) : HasDerivAt (right1 α) (right2 α u) u := by
  have hi : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id u
  unfold right1 right2
  have h := (((((hi.const_sub 1).pow 2).div_const 2).add
    ((hi.const_sub 1).const_mul (B1 α))).add_const (B2 α/2))
  convert! h using 1 <;> norm_num <;> ring

theorem right2_deriv (α u : ℝ) : HasDerivAt (right2 α) 1 u := by
  unfold right2
  exact ((hasDerivAt_id u).sub_const 1).sub_const (B1 α)

theorem left0_deriv (α u : ℝ) : HasDerivAt (left0 α) (left1 α u) u := by
  have hi : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id u
  unfold left0 left1
  have h := ((((hi.const_sub α).pow 2).div_const 2).add (right0_deriv α u))
  convert! h using 1 <;> norm_num <;> ring

theorem left1_deriv (α u : ℝ) : HasDerivAt (left1 α) (left2 α u) u := by
  have hi : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id u
  unfold left1 left2
  have h := (((hi.const_sub α).neg).add (right1_deriv α u))
  convert! h using 1 <;> norm_num [right2] <;> ring

theorem left2_deriv (α u : ℝ) : HasDerivAt (left2 α) 1 u := by
  unfold left2
  exact (hasDerivAt_id u).sub_const (B1 α)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem integrate_three (a b : ℝ) (p0 p1 p2 : ℝ → ℝ) (f0 f1 f2 f3 : ℝ → F)
    (hp0 : ∀ u, HasDerivAt p0 (p1 u) u) (hp1 : ∀ u, HasDerivAt p1 (p2 u) u)
    (hp2 : ∀ u, HasDerivAt p2 1 u)
    (hf0 : ∀ u ∈ uIcc a b, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u ∈ uIcc a b, HasDerivAt f1 (f2 u) u)
    (hf2 : ∀ u ∈ uIcc a b, HasDerivAt f2 (f3 u) u)
    (hi1 : IntervalIntegrable f1 volume a b) (hi2 : IntervalIntegrable f2 volume a b)
    (hi3 : IntervalIntegrable f3 volume a b) :
    (∫ u in a..b, p0 u • f3 u) =
      p0 b • f2 b-p0 a • f2 a-p1 b • f1 b+p1 a • f1 a+
      p2 b • f0 b-p2 a • f0 a-(∫ u in a..b, f0 u) := by
  have hc1 : Continuous p1 := continuous_iff_continuousAt.mpr (fun u => (hp1 u).continuousAt)
  have hc2 : Continuous p2 := continuous_iff_continuousAt.mpr (fun u => (hp2 u).continuousAt)
  have h0 := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (fun u _ => hp0 u) hf2 (hc1.intervalIntegrable a b) hi3
  have h1 := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (fun u _ => hp1 u) hf1 (hc2.intervalIntegrable a b) hi2
  have h2 := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (fun u _ => hp2 u) hf0 (continuous_const.intervalIntegrable a b) hi1
  simp only [one_smul] at h2
  rw [h1,h2] at h0
  rw [h0]
  abel

theorem cell_identity (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (f0 f1 f2 f3 : ℝ → F)
    (hf0 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f1 (f2 u) u)
    (hf2 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f2 (f3 u) u)
    (hf3 : ContinuousOn f3 (Icc (0:ℝ) 1)) :
    f0 α-(∫ u in (0:ℝ)..1, f0 u)-B1 α • (f0 1-f0 0)-(B2 α/2) • (f1 1-f1 0) =
      (∫ u in (0:ℝ)..α, left0 α u • f3 u)+(∫ u in α..1, right0 α u • f3 u) := by
  have hleft : uIcc (0:ℝ) α ⊆ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hα0]
    exact Icc_subset_Icc le_rfl hα1
  have hright : uIcc α (1:ℝ) ⊆ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hα1]
    exact Icc_subset_Icc hα0 le_rfl
  have hc0 : ContinuousOn f0 (Icc (0:ℝ) 1) :=
    fun u hu => (hf0 u hu).continuousAt.continuousWithinAt
  have hc1 : ContinuousOn f1 (Icc (0:ℝ) 1) :=
    fun u hu => (hf1 u hu).continuousAt.continuousWithinAt
  have hc2 : ContinuousOn f2 (Icc (0:ℝ) 1) :=
    fun u hu => (hf2 u hu).continuousAt.continuousWithinAt
  have hl := integrate_three 0 α (left0 α) (left1 α) (left2 α) f0 f1 f2 f3
    (left0_deriv α) (left1_deriv α) (left2_deriv α)
    (fun u hu => hf0 u (hleft hu)) (fun u hu => hf1 u (hleft hu)) (fun u hu => hf2 u (hleft hu))
    (hc1.mono hleft).intervalIntegrable (hc2.mono hleft).intervalIntegrable (hf3.mono hleft).intervalIntegrable
  have hr := integrate_three α 1 (right0 α) (right1 α) (right2 α) f0 f1 f2 f3
    (right0_deriv α) (right1_deriv α) (right2_deriv α)
    (fun u hu => hf0 u (hright hu)) (fun u hu => hf1 u (hright hu)) (fun u hu => hf2 u (hright hu))
    (hc1.mono hright).intervalIntegrable (hc2.mono hright).intervalIntegrable (hf3.mono hright).intervalIntegrable
  have hj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc0.mono hleft).intervalIntegrable (hc0.mono hright).intervalIntegrable
  rw [hl,hr,← hj]
  simp only [left0,left1,left2,right0,right1,right2,B1,B2]
  module

end
end Borwein.PeanoQuadrature


